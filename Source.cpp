// Win32 Bitmap Visualizer for Expressions 1..9 (ascending)
// ... (ヘッダー省略) ...

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <windowsx.h>
#include <stdint.h>
#include <vector>
#include <string>
#include <atomic>
#include <memory>
#include <algorithm>
#include <chrono>

#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")

// -------- Boost big rational ----------
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/rational.hpp>

using BigInt = boost::multiprecision::cpp_int;
using BigRat = boost::rational<BigInt>;

// --------------- UI constants ----------------
enum : int {
    IDC_START = 1001,
    IDC_CANCEL,
    IDC_STATUS,
    IDC_CURRENT_EXPR,
    IDC_CONCAT_CHECK,
    IDC_OPS_EDIT,
    IDC_MAXMASKS_EDIT,
    IDC_MAXTREES_EDIT,
};

static const int BMP_W = 100;
static const int BMP_H = 112; // 100 * 112 = 11200 >= 11111
static const int MAX_N = 11111;

static const wchar_t* kDefaultOps = L"+-*/^";
static const bool     kDefaultConcatOn = true;

// 探索セーフティ（既定値。保守的な値に変更済）
static const uint32_t kDefaultMaxMasks = 64;  // 連結マスクの上限
static const uint32_t kDefaultMaxTrees = 200000; // 1構成当たりの括弧木枚数の上限
static const BigInt kMaxExponent = 1000000; // 許容する最大指数値

static std::atomic<bool> g_running{ false };
static std::atomic<bool> g_cancel{ false };
static HANDLE g_hWorker = nullptr;

// --------------- Bitmap buffer ---------------
static std::vector<uint8_t> g_map; // 0/1 flags: index 1..11111 mapped to pixels
static BITMAPINFO g_bmi;
static std::vector<uint32_t> g_pixels; // ARGB 32-bit, top-down for StretchDIBits

// Map number [1..MAX_N] to pixel (x,y)
static inline bool num_to_xy(int n, int& x, int& y) {
    if (n < 1 || n > MAX_N) return false;
    int idx = n - 1;
    x = idx % BMP_W;
    y = idx / BMP_W;
    return true;
}

// Update g_pixels from g_map
static void refresh_pixels() {
    // background: dark gray, on: white
    for (int y = 0; y < BMP_H; ++y) {
        for (int x = 0; x < BMP_W; ++x) {
            int idx = y * BMP_W + x;
            bool on = (idx < MAX_N) ? (g_map[idx + 1] != 0) : false;
            uint8_t c = on ? 255 : 50;
            uint32_t argb = 0xFF000000u | (c << 16) | (c << 8) | c;
            g_pixels[idx] = argb;
        }
    }
}

// -------------- Expression enumeration ----------

struct Node {
    // Expression tree node: either leaf (value) or op(left,right)
    bool isLeaf = false;
    std::wstring text;    // pretty string
    BigRat val;           // value (valid if valid==true)
    bool valid = true;    // becomes false on invalid (e.g., div by zero, bad exponent)
    wchar_t op = 0;
    std::unique_ptr<Node> L, R;
};

// 深いコピー（ディープコピー）
static std::unique_ptr<Node> clone_node(const std::unique_ptr<Node>& src) {
    if (!src) return nullptr;
    auto n = std::make_unique<Node>();
    n->isLeaf = src->isLeaf;
    n->text = src->text;
    n->val = src->val;
    n->valid = src->valid;
    n->op = src->op;
    n->L = clone_node(src->L);
    n->R = clone_node(src->R);
    return n;
}

// Check if rational is integer
static inline bool is_integer(const BigRat& r) {
    return r.denominator() == 1;
}

// Safe power: a ^ b; b must be integer
static BigRat pow_int(const BigRat& a, const BigInt& b, bool& ok) {
    ok = true;
    if (b == 0) return BigRat(1);

    // キャンセルチェック
    if (g_cancel.load()) { ok = false; return BigRat(0); }

    if (b < 0) {
        if (a.numerator() == 0) { ok = false; return BigRat(0); }
        BigRat inv = BigRat(a.denominator(), a.numerator());
        BigInt pos = -b;
        BigRat base = inv;
        BigRat res = BigRat(1);
        BigInt e = pos;
        while (e != 0) {
            // ループ内でのキャンセルチェック
            if (g_cancel.load()) { ok = false; return BigRat(0); }

            if ((e & 1) != 0) res *= base;
            base *= base;
            e >>= 1;
        }
        return res;
    }
    BigRat base = a;
    BigRat res = BigRat(1);
    BigInt e = b;
    while (e != 0) {
        // ループ内でのキャンセルチェック
        if (g_cancel.load()) { ok = false; return BigRat(0); }

        if ((e & 1) != 0) res *= base;
        base *= base;
        e >>= 1;
    }
    return res;
}

// Evaluate node recursively
static void eval_node(Node* n) {
    if (!n) return;

    // eval_nodeの再帰開始時のキャンセルチェック (フリーズ対策)
    if (g_cancel.load()) { n->valid = false; return; }

    if (n->isLeaf) return; // leaf already has value

    eval_node(n->L.get());
    eval_node(n->R.get());
    if (!n->L->valid || !n->R->valid) { n->valid = false; return; }

    const BigRat& A = n->L->val;
    const BigRat& B = n->R->val;

    switch (n->op) {
    case L'+':
        n->val = A + B; break;
    case L'-':
        n->val = A - B; break;
    case L'*':
        n->val = A * B; break;
    case L'/':
        if (B.numerator() == 0) { n->valid = false; return; }
        n->val = A / B; break;
    case L'^':
        // 1. 指数が整数であることを確認 (分数累乗を排除)
        if (!is_integer(B)) { n->valid = false; return; }

        // 2. 指数が非負の整数であることを確認 (負の整数累乗を排除)
        if (B.numerator() < 0) { n->valid = false; return; }

        {
            BigInt exponent = B.numerator();

            // 指数が許容最大値を超えていないかチェック
            if (exponent > kMaxExponent) {
                n->valid = false; return;
            }

            bool ok = true;
            n->val = pow_int(A, exponent, ok);
            if (!ok) { n->valid = false; return; }
        }
        break;
    default:
        n->valid = false; return;
    }
}

// Build all operands strings by concatenation mask (8 bits)
static void build_operands(uint8_t mask, std::vector<std::wstring>& out) {
    out.clear();
    std::wstring cur = L"1";
    for (int i = 0; i < 8; ++i) {
        wchar_t d = L'2' + i; // 2..9
        if (mask & (1u << i)) {
            cur.push_back(d);
        }
        else {
            out.push_back(cur);
            cur.assign(1, d);
        }
    }
    out.push_back(cur);
}

// Build leaf nodes (values) from operands strings
static void make_leaves(const std::vector<std::wstring>& ops, std::vector<std::unique_ptr<Node>>& leaves) {
    leaves.clear();
    leaves.reserve(ops.size());
    for (const auto& s : ops) {
        // parse as integer (base 10)
        BigInt v = 0;
        for (wchar_t c : s) {
            v *= 10;
            v += (int)(c - L'0');
        }
        auto n = std::make_unique<Node>();
        n->isLeaf = true;
        n->text = s;
        n->val = BigRat(v); // exact integer
        n->valid = true;
        leaves.push_back(std::move(n));
    }
}

// Enumerate operator vectors of length k over allowed set
static bool nextOpVector(std::vector<int>& idx, int base) {
    for (int p = (int)idx.size() - 1; p >= 0; --p) {
        if (++idx[p] < base) return true;
        idx[p] = 0;
    }
    return false;
}

// Build parenthesized trees over [i..j]
static void genTreesRec(int i, int j,
    const std::vector<std::unique_ptr<Node>>& leaves,
    const std::vector<wchar_t>& ops, // ops[m] is operator at position m
    std::vector<std::unique_ptr<Node>>& out,
    uint32_t& budgetTrees, bool& aborted) {
    if (aborted) return;

    // キャンセルチェック (高速キャンセル応答のため)
    if (g_cancel.load()) { aborted = true; return; }

    if (i == j) {
        auto n = std::make_unique<Node>();
        n->isLeaf = true;
        n->text = leaves[i]->text;
        n->val = leaves[i]->val;
        n->valid = true;
        out.push_back(std::move(n));
        return;
    }
    for (int m = i; m < j; ++m) {
        std::vector<std::unique_ptr<Node>> Ls, Rs;

        genTreesRec(i, m, leaves, ops, Ls, budgetTrees, aborted);
        if (aborted) return; // 再帰呼び出し後にもチェック

        genTreesRec(m + 1, j, leaves, ops, Rs, budgetTrees, aborted);
        if (aborted) return; // 再帰呼び出し後にもチェック

        for (auto& L : Ls) {
            for (auto& R : Rs) {
                if (aborted) return;
                if (budgetTrees == 0) { aborted = true; return; }
                --budgetTrees;

                auto n = std::make_unique<Node>();
                n->op = ops[(size_t)m];
                n->isLeaf = false;

                // 文字列構築（L/Rはこのループ内で有効）
                n->text.reserve(L->text.size() + R->text.size() + 4);
                n->text.push_back(L'(');
                n->text += L->text; n->text.push_back(L' ');
                n->text.push_back(n->op); n->text.push_back(L' ');
                n->text += R->text; n->text.push_back(L')');

                // ★ ムーブではなくディープコピーで安全に複製
                n->L = clone_node(L);
                n->R = clone_node(R);

                out.push_back(std::move(n));
            }
        }
    }
}

// -------------- UI Status Helpers ------------------
// ★ 修正点: set_status と set_current_expr の定義をここに移動
static void set_status(HWND hWnd, const std::wstring& s) {
    SetWindowTextW(GetDlgItem(hWnd, IDC_STATUS), s.c_str());
}

static void set_current_expr(HWND hWnd, const std::wstring& s) {
    SetWindowTextW(GetDlgItem(hWnd, IDC_CURRENT_EXPR), s.c_str());
}

// Evaluate all trees, mark integers in [1..11111]
// HWND hWnd を引数に追加
static void eval_and_mark(std::vector<std::unique_ptr<Node>>& trees, std::vector<uint8_t>& mark, HWND hWnd) {
    for (auto& t : trees) {
        // 各ノードの評価前にキャンセルをチェック
        if (g_cancel.load()) return;

        // 式を表示 (計算直前)
        set_current_expr(hWnd, t->text);
        RedrawWindow(GetDlgItem(hWnd, IDC_CURRENT_EXPR), nullptr, nullptr, RDW_INVALIDATE | RDW_UPDATENOW);

        // UIスレッドに処理を返す機会を与える (遅延を許容して確実な表示を優先)
        Sleep(1);

        eval_node(t.get());
        if (!t->valid) continue;
        if (!is_integer(t->val)) continue;
        BigInt n = t->val.numerator(); // denominator == 1
        if (n <= 0) continue;
        if (n <= MAX_N) {
            // convert to small int fast (<=11111)
            int v = 0;
            std::string s = n.convert_to<std::string>();
            v = std::stoi(s);
            mark[(size_t)v] = 1;
        }
    }
}

// -------------- Worker thread ------------------
struct WorkerArgs {
    HWND hWnd;
    bool useConcat;
    std::wstring opsSet; // + - * / ^
    uint32_t maxMasks;    // limit masks for safety
    uint32_t maxTrees;    // per (mask, opvector) generation cap
};


static DWORD WINAPI WorkerProc(LPVOID lp) {
    std::unique_ptr<WorkerArgs> u((WorkerArgs*)lp);
    HWND hWnd = u->hWnd;

    // reset map
    std::fill(g_map.begin(), g_map.end(), 0);

    const int opsBase = (int)u->opsSet.size();
    uint32_t maskBegin = 0, maskEnd = u->useConcat ? 256u : 1u;
    if (u->maxMasks < (maskEnd - maskBegin)) maskEnd = maskBegin + u->maxMasks;

    uint64_t evalCount = 0;
    uint32_t lastPaint = GetTickCount();

    // 探索開始時に式の表示領域をクリア
    set_current_expr(hWnd, L"Starting enumeration...");

    for (uint32_t mask = maskBegin; mask < maskEnd && !g_cancel.load(); ++mask) {
        std::vector<std::wstring> operandsStr;
        build_operands((uint8_t)mask, operandsStr);
        const int k = (int)operandsStr.size() - 1;

        std::vector<std::unique_ptr<Node>> leaves;
        make_leaves(operandsStr, leaves);

        if (k <= 0) {
            // Single number; mark directly if within range
            BigInt n = 0;
            for (wchar_t c : operandsStr[0]) {
                n *= 10; n += (int)(c - L'0');
            }
            if (n >= 1 && n <= MAX_N) {
                int v = std::stoi(n.convert_to<std::string>());
                g_map[(size_t)v] = 1;
            }

            // periodic repaint
            uint32_t now = GetTickCount();
            if (now - lastPaint > 150) {
                refresh_pixels();
                // RedrawWindowに変更 (フリーズ対策)
                RedrawWindow(hWnd, nullptr, nullptr, RDW_INVALIDATE | RDW_UPDATENOW);
                wchar_t buf[256];
                std::swprintf(buf, 256, L"mask %u/%u | trees(eval)≈ %llu | dots=%u",
                    (unsigned)mask + 1, (unsigned)maskEnd,
                    (unsigned long long)evalCount,
                    (unsigned)std::count(g_map.begin(), g_map.end(), (uint8_t)1));
                set_status(hWnd, buf);
                // 単一数の場合は、その数を式として表示
                set_current_expr(hWnd, operandsStr.empty() ? L"N/A" : operandsStr[0]);
                lastPaint = now;
            }
            // Sleep(1)を強制 (フリーズ対策)
            Sleep(1);
            continue;
        }

        // enumerate operator vectors
        std::vector<int> idx(k, 0);
        do {
            // build operator char list
            std::vector<wchar_t> ops; ops.resize(k);
            for (int i = 0; i < k; ++i) ops[i] = u->opsSet[(size_t)idx[i]];

            // enumerate parenthesizations (trees)
            std::vector<std::unique_ptr<Node>> trees;
            uint32_t budget = u->maxTrees;
            bool aborted = false;

            // 全ての式を生成
            genTreesRec(0, k, leaves, ops, trees, budget, aborted);

            // genTreesRec()でキャンセルされたか、または木が一つも生成されなかったらスキップ
            if (g_cancel.load() || trees.empty()) {
                if (g_cancel.load()) break; // キャンセルの場合はdo-whileを抜ける
                Sleep(1);
                continue;
            }

            // evaluate and mark - 各式を評価する直前に表示を行います
            // hWndを渡して eval_and_mark 内で UI を更新
            eval_and_mark(trees, g_map, hWnd);
            evalCount += trees.size();

            // eval_and_mark()でキャンセルされたかチェック
            if (g_cancel.load()) break;

            // periodic repaint
            uint32_t now = GetTickCount();
            if (now - lastPaint > 150) {
                refresh_pixels();
                // RedrawWindowに変更 (フリーズ対策)
                RedrawWindow(hWnd, nullptr, nullptr, RDW_INVALIDATE | RDW_UPDATENOW);
                wchar_t buf[256];
                std::swprintf(buf, 256, L"mask %u/%u | trees(eval)≈ %llu | dots=%u",
                    (unsigned)mask + 1, (unsigned)maskEnd,
                    (unsigned long long)evalCount,
                    (unsigned)std::count(g_map.begin(), g_map.end(), (uint8_t)1));
                set_status(hWnd, buf);

                lastPaint = now;
            }

            // Sleep(1)を強制 (フリーズ対策)
            Sleep(1);

            if (g_cancel.load()) break;
        } while (nextOpVector(idx, opsBase) && !g_cancel.load());

        if (g_cancel.load()) break;
    }

    refresh_pixels();
    InvalidateRect(hWnd, nullptr, FALSE); // 最終更新はキューに追加でOK
    wchar_t fin[256];
    std::swprintf(fin, 256, L"Finished. trees(eval)≈ %llu | dots=%u",
        (unsigned long long)evalCount,
        (unsigned)std::count(g_map.begin(), g_map.end(), (uint8_t)1));
    set_status(hWnd, fin);

    // 探索終了時、式の表示をリセット
    set_current_expr(hWnd, L"Finished.");

    g_running = false;

    // 探索終了後にボタンの状態をリセット
    EnableWindow(GetDlgItem(hWnd, IDC_START), TRUE);
    EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), FALSE);

    return 0;
}

// --------------- Rendering -----------------------
static void draw_bitmap(HWND hWnd, HDC hdc) {
    RECT rc; GetClientRect(hWnd, &rc);
    // コントロール領域の高さを定義 (描画重なり対策)
    static const int panelH = 90;
    int W = rc.right - rc.left;
    int H = rc.bottom - rc.top - panelH; // ビットマップに使用できる高さを計算

    int dstW = W - 20;
    int dstH = H - 20;
    if (dstW < BMP_W) dstW = BMP_W;
    if (dstH < BMP_H) dstH = BMP_H;

    int x = 10;
    // 描画開始Y座標をコントロール領域の下に移動 (描画重なり対策)
    int y = panelH + 10;

    StretchDIBits(hdc,
        x, y, dstW, dstH,
        0, 0, BMP_W, BMP_H,
        g_pixels.data(), &g_bmi, DIB_RGB_COLORS, SRCCOPY);
}

// --------------- Win32 UI -----------------------
static LRESULT CALLBACK WndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_CREATE: {
        // init bitmap buffers
        g_map.assign(MAX_N + 1, 0);
        g_pixels.assign(BMP_W * BMP_H, 0xFF202020);
        ZeroMemory(&g_bmi, sizeof(g_bmi));
        g_bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
        g_bmi.bmiHeader.biWidth = BMP_W;
        g_bmi.bmiHeader.biHeight = -BMP_H; // top-down
        g_bmi.bmiHeader.biPlanes = 1;
        g_bmi.bmiHeader.biBitCount = 32;
        g_bmi.bmiHeader.biCompression = BI_RGB;

        int y = 0;
        // 1行目: Start/Cancel, Options (y=10)
        CreateWindowW(L"BUTTON", L"Start", WS_CHILD | WS_VISIBLE, 10, y + 10, 80, 24, hWnd, (HMENU)IDC_START, 0, 0);
        CreateWindowW(L"BUTTON", L"Cancel", WS_CHILD | WS_VISIBLE | WS_DISABLED, 100, y + 10, 80, 24, hWnd, (HMENU)IDC_CANCEL, 0, 0);

        CreateWindowW(L"BUTTON", L"Concatenation (12, 123 ...)", WS_CHILD | WS_VISIBLE | BS_AUTOCHECKBOX,
            200, y + 10, 220, 24, hWnd, (HMENU)IDC_CONCAT_CHECK, 0, 0);
        SendMessageW(GetDlgItem(hWnd, IDC_CONCAT_CHECK), BM_SETCHECK, kDefaultConcatOn ? BST_CHECKED : BST_UNCHECKED, 0);

        CreateWindowW(L"STATIC", L"Ops (+-*/^):", WS_CHILD | WS_VISIBLE, 440, y + 10 + 3, 90, 18, hWnd, 0, 0, 0);
        CreateWindowW(L"EDIT", kDefaultOps, WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
            530, y + 10, 100, 24, hWnd, (HMENU)IDC_OPS_EDIT, 0, 0);

        CreateWindowW(L"STATIC", L"Max masks:", WS_CHILD | WS_VISIBLE, 650, y + 10 + 3, 80, 18, hWnd, 0, 0, 0);
        wchar_t mm[32]; std::swprintf(mm, 32, L"%u", kDefaultMaxMasks);
        CreateWindowW(L"EDIT", mm, WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
            730, y + 10, 70, 24, hWnd, (HMENU)IDC_MAXMASKS_EDIT, 0, 0);

        CreateWindowW(L"STATIC", L"Max trees/opvec:", WS_CHILD | WS_VISIBLE, 820, y + 10 + 3, 110, 18, hWnd, 0, 0, 0);
        wchar_t mt[32]; std::swprintf(mt, 32, L"%u", kDefaultMaxTrees);
        CreateWindowW(L"EDIT", mt, WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
            930, y + 10, 90, 24, hWnd, (HMENU)IDC_MAXTREES_EDIT, 0, 0);

        // 2行目: 現在の式表示 (y=40)
        CreateWindowW(L"STATIC", L"Expression:", WS_CHILD | WS_VISIBLE,
            10, y + 40, 90, 18, hWnd, 0, 0, 0);
        CreateWindowW(L"STATIC", L"", WS_CHILD | WS_VISIBLE | WS_BORDER | ES_READONLY,
            100, y + 40, 920, 18, hWnd, (HMENU)IDC_CURRENT_EXPR, 0, 0);

        // 3行目: Status (y=65)
        CreateWindowW(L"STATIC", L"Status:", WS_CHILD | WS_VISIBLE,
            10, y + 65, 90, 18, hWnd, 0, 0, 0);
        CreateWindowW(L"STATIC", L"Ready.", WS_CHILD | WS_VISIBLE,
            100, y + 65, 920, 18, hWnd, (HMENU)IDC_STATUS, 0, 0);

        return 0;
    }
    case WM_COMMAND: {
        switch (LOWORD(wParam)) {
        case IDC_START: {
            if (g_running.load()) break;
            g_cancel = false; g_running = true;

            EnableWindow(GetDlgItem(hWnd, IDC_START), FALSE);
            EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), TRUE);

            struct WorkerArgs* args = new WorkerArgs();
            args->hWnd = hWnd;
            args->useConcat = (SendMessageW(GetDlgItem(hWnd, IDC_CONCAT_CHECK), BM_GETCHECK, 0, 0) == BST_CHECKED);

            // sanitize ops
            std::wstring ops; ops.resize(256);
            int n = GetWindowTextW(GetDlgItem(hWnd, IDC_OPS_EDIT), &ops[0], 256);
            ops.resize((n > 0) ? n : 0);
            std::wstring clean;
            for (wchar_t c : ops) {
                if (c == L'+' || c == L'-' || c == L'*' || c == L'/' || c == L'^') clean.push_back(c);
            }
            if (clean.empty()) clean = kDefaultOps;
            args->opsSet = clean;

            auto readUInt = [](HWND h, int id, uint32_t def)->uint32_t {
                wchar_t buf[64] = { 0 }; GetWindowTextW(GetDlgItem(h, id), buf, 64);
                if (!buf[0]) return def;
                uint64_t v = 0; for (const wchar_t* p = buf; *p; ++p) {
                    if (*p < L'0' || *p>L'9') return def; v = v * 10 + (*p - L'0');
                }
                if (v == 0) return def;
                if (v > 0xFFFFFFFFull) v = 0xFFFFFFFFull;
                return (uint32_t)v;
                };
            args->maxMasks = readUInt(hWnd, IDC_MAXMASKS_EDIT, kDefaultMaxMasks);
            args->maxTrees = readUInt(hWnd, IDC_MAXTREES_EDIT, kDefaultMaxTrees);

            DWORD tid = 0;
            g_hWorker = CreateThread(nullptr, 0, WorkerProc, args, 0, &tid);
            if (!g_hWorker) {
                g_running = false;
                MessageBoxW(hWnd, L"Failed to create worker thread.", L"Error", MB_ICONERROR);
                EnableWindow(GetDlgItem(hWnd, IDC_START), TRUE);
                EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), FALSE);
            }
            break;
        }
        case IDC_CANCEL: {
            if (g_running.load()) {
                g_cancel = true;
                EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), FALSE);
            }
            break;
        }
        }
        return 0;
    }
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC hdc = BeginPaint(hWnd, &ps);
        draw_bitmap(hWnd, hdc);
        EndPaint(hWnd, &ps);
        return 0;
    }
    case WM_SIZE: {
        InvalidateRect(hWnd, nullptr, TRUE);
        return 0;
    }
    case WM_CLOSE: {
        if (g_running.load()) {
            if (IDYES == MessageBoxW(hWnd, L"Enumeration is running. Cancel and exit?", L"Confirm", MB_YESNO | MB_ICONQUESTION)) {
                g_cancel = true;
                if (g_hWorker) {
                    WaitForSingleObject(g_hWorker, INFINITE);
                    CloseHandle(g_hWorker);
                    g_hWorker = nullptr;
                }
                DestroyWindow(hWnd);
            }
            return 0;
        }
        DestroyWindow(hWnd);
        return 0;
    }
    case WM_DESTROY: {
        PostQuitMessage(0);
        return 0;
    }
    }
    return DefWindowProcW(hWnd, msg, wParam, lParam);
}

int APIENTRY wWinMain(HINSTANCE hInst, HINSTANCE, LPWSTR, int) {
    const wchar_t* cls = L"ExprDotMapWin32";

    WNDCLASSW wc{};
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.lpszClassName = cls;
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    RegisterClassW(&wc);

    HWND hWnd = CreateWindowW(cls, L"1..9 Expressions → 1..11111 Dot Map (Boost Big Rational)",
        WS_OVERLAPPEDWINDOW,
        CW_USEDEFAULT, CW_USEDEFAULT, 1100, 760,
        nullptr, nullptr, hInst, nullptr);

    ShowWindow(hWnd, SW_SHOW);
    UpdateWindow(hWnd);

    MSG msg;
    while (GetMessageW(&msg, nullptr, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }
    return 0;
}