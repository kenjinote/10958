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
#include <thread>
#include <cmath>
#include <fstream>
#include <cstdio>
#include <stdexcept>
#include <stdio.h>
#include <functional> // for std::function

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
};

static const int BMP_W = 100;
static const int BMP_H = 112;
static const int MAX_N = 11111;

static const wchar_t* kDefaultOps = L"+-*/^";
static const bool kDefaultConcatOn = true;

// 固定値として定義された最大値 (Catala数 1430, マスク数 256)
static const uint32_t kDefaultMaxMasks = 256;
static const uint32_t kDefaultMaxTrees = 1430;
static const BigInt kMaxExponent = 1000000;

static std::atomic<bool> g_running{ false };
static std::atomic<bool> g_cancel{ false };
static std::vector<HANDLE> g_hWorkers;

#define IDT_REPAINT 1

// 永続化用グローバル変数と定数
static const wchar_t* kStateFile = L"result_state.dat";
static const uint32_t kSaveIntervalMs = 5000; // 5秒ごとに保存
static std::atomic<uint32_t> g_current_mask_processing{ 0 };
static auto g_last_save_time = std::chrono::steady_clock::now();

// 稼働スレッド数と追跡式コンテナ
static std::vector<std::wstring> g_current_expressions_by_thread;
static std::atomic<size_t> g_active_thread_count{ 0 };

// 初回実行時の論理コア数を保持
static const unsigned int s_initial_thread_count = std::thread::hardware_concurrency();

// --------------- Bitmap buffer ---------------
static std::vector<uint8_t> g_map;
static BITMAPINFO g_bmi;
static std::vector<uint32_t> g_pixels;
static std::vector<std::wstring> g_expressions;

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
    bool isLeaf = false;
    std::wstring text;
    BigRat val;
    bool valid = true;
    wchar_t op = 0;
    std::unique_ptr<Node> L, R;
};

// 安定化のためのディープコピー関数を再導入
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

    if (b < 0) {
        if (a.numerator() == 0) { ok = false; return BigRat(0); }
        BigRat inv(a.denominator(), a.numerator());
        BigInt pos = -b;
        BigRat base = inv;
        BigRat res(1);

        BigInt e = pos;
        while (e != 0) {
            if (g_cancel.load()) { ok = false; return BigRat(0); }
            if ((e & 1) != 0) res *= base;
            base *= base;
            e >>= 1;
        }
        return res;
    }

    BigRat base = a;
    BigRat res(1);
    BigInt e = b;

    while (e != 0) {
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

    if (n->isLeaf) return;

    // ★修正: べき乗演算子の場合の評価順序を分離
    if (n->op == L'^') {
        eval_node(n->L.get());
        if (!n->L->valid) { n->valid = false; return; }

        const BigRat& A = n->L->val;

        // 1. ベース A が 1 かチェック (1^N = 1 特例)
        if (A.numerator() == 1 && A.denominator() == 1) {
            n->val = BigRat(1);
            // 指数Bの評価はスキップし、有効性はtrueにする
            // n->R->valid = true; // Rのvalidは変更しない
            return;
        }

        // 2. 指数Bの評価を実行
        eval_node(n->R.get());
        if (!n->R->valid) { n->valid = false; return; }

    }
    else {
        // 通常の二項演算の場合は、両方のオペランドの評価を続行
        eval_node(n->L.get());
        eval_node(n->R.get());
        if (!n->L->valid || !n->R->valid) { n->valid = false; return; }
    }

    // 両オペランドの評価結果を取得
    const BigRat& A = n->L->val;
    const BigRat& B_val = n->R->val;

    switch (n->op) {
    case L'+':
        n->val = A + B_val; break;
    case L'-':
        n->val = A - B_val; break;
    case L'*':
        n->val = A * B_val; break;
    case L'/':
        if (B_val.numerator() == 0) { n->valid = false; return; }
        n->val = A / B_val; break;
    case L'^':
        // 1. 指数が整数であることを確認
        if (!is_integer(B_val)) { n->valid = false; return; }

        {
            BigInt B_int = B_val.numerator();

            // 符号反転をシミュレートする結果のリスト (指数は正であるべき)
            BigInt exponent = (B_int < 0) ? -B_int : B_int;

            // 2. 許容最大値を超えていないかチェック
            if (exponent > kMaxExponent) { n->valid = false; return; }

            bool ok = true;
            BigRat current_val = pow_int(A, exponent, ok);

            if (ok) {
                n->val = current_val;
            }
            else {
                n->valid = false;
                return;
            }
        }
        break;
    default:
        n->valid = false; return;
    }

    // 高速化のための枝刈り (Bound Check)
    // べき乗の結果も含む、全ての中間結果が 200,000 を超える場合はここで枝刈り
    const BigInt max_numerator_threshold = BigInt(200000);
    BigInt abs_num = (n->val.numerator() < 0) ? -n->val.numerator() : n->val.numerator();

    if (n->val.denominator() > BigInt(100000) || abs_num > max_numerator_threshold) {
        n->valid = false;
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
// 修正: 正のオペランドのみを生成するように戻す
static void make_leaves(const std::vector<std::wstring>& ops, std::vector<std::unique_ptr<Node>>& leaves) {
    leaves.clear();
    leaves.reserve(ops.size());

    for (const auto& s : ops) {
        // 1. 正のオペランドのみを生成
        BigInt v_pos = 0;
        for (wchar_t c : s) {
            v_pos *= 10;
            v_pos += (int)(c - L'0');
        }
        // 正のノードを追加
        auto n_pos = std::make_unique<Node>();
        n_pos->isLeaf = true;
        n_pos->text = s;
        n_pos->val = BigRat(v_pos);
        n_pos->valid = true;
        leaves.push_back(std::move(n_pos));
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
// leaves は k 個の正のオペランド、ops は k-1 個の演算子を受け取る
static void genTreesRec(int i, int j,
    const std::vector<std::unique_ptr<Node>>& leaves,
    const std::vector<wchar_t>& ops,
    std::vector<std::unique_ptr<Node>>& out,
    uint32_t& budgetTrees, bool& aborted) {
    if (aborted) return;

    if (g_cancel.load()) { aborted = true; return; }

    if (i == j) {
        // 葉ノードのディープコピーを追加
        out.push_back(clone_node(leaves[i]));
        return;
    }
    for (int m = i; m < j; ++m) {
        std::vector<std::unique_ptr<Node>> Ls, Rs;

        // m は leaves のインデックス。ops のインデックスとして使用
        genTreesRec(i, m, leaves, ops, Ls, budgetTrees, aborted);
        if (aborted) return;

        genTreesRec(m + 1, j, leaves, ops, Rs, budgetTrees, aborted);
        if (aborted) return;

        for (const std::unique_ptr<Node>& L : Ls) {
            for (const std::unique_ptr<Node>& R : Rs) {
                if (aborted) return;
                if (budgetTrees == 0) { aborted = true; return; }
                --budgetTrees;

                auto n = std::make_unique<Node>();
                n->op = ops[(size_t)m]; // m が ops のインデックスに対応
                n->isLeaf = false;

                // 文字列構築 (L + op + R)
                n->text.reserve(L->text.size() + R->text.size() + 4);
                n->text.push_back(L'(');
                n->text += L->text; n->text.push_back(L' ');
                n->text.push_back(n->op); n->text.push_back(L' ');
                n->text += R->text; n->text.push_back(L')');

                // 安定したディープコピーを使用
                n->L = clone_node(L);
                n->R = clone_node(R);

                out.push_back(std::move(n));
            }
        }
    }
}


// -------------- UI Status Helpers ------------------

static void set_status(HWND hWnd, const std::wstring& s) {
    SetWindowTextW(GetDlgItem(hWnd, IDC_STATUS), s.c_str());
}

// NOTE: IDC_CURRENT_EXPR はマウスオーバーと計算中の式表示で共有される
static void set_current_expr(HWND hWnd, const std::wstring& s) {
    // マウスオーバー時以外（計算中の式表示）は、ステータスバー下の領域を使用
    SetWindowTextW(GetDlgItem(hWnd, IDC_CURRENT_EXPR), s.c_str());
}

// Evaluate all trees, mark integers in [1..11111]
static uint64_t eval_and_mark(std::vector<std::unique_ptr<Node>>& trees, std::vector<uint8_t>& mark) {
    uint64_t count = 0;

    for (auto& t : trees) {
        if (g_cancel.load()) return count;

        eval_node(t.get());
        if (!t->valid) continue;

        // 最終結果が整数でない場合は無視
        if (!is_integer(t->val)) continue;

        BigInt n = t->val.numerator();

        // ゼロまたは負の結果は無視 (N >= 1 のみ許可)
        if (n < 1) continue;

        BigInt abs_n = n;

        if (abs_n >= 1 && abs_n <= MAX_N) {
            // 絶対値 (1から11111) にマップ
            int v = 0;
            try {
                std::string s = abs_n.convert_to<std::string>();
                v = std::stoi(s);
            }
            catch (const std::exception&) {
                continue;
            }

            // 正しいインデックス範囲内か確認
            if (v >= 1 && v <= MAX_N) {
                if (mark[(size_t)v] == 0) {
                    mark[(size_t)v] = 1;
                    g_expressions[(size_t)v] = t->text;
                }
            }
        }
        count++;
    }
    return count;
}

// ----------------- Persistence Logic -------------------

struct PersistenceData {
    uint32_t next_mask_start;
    uint64_t total_eval_count;
    unsigned int initial_thread_count;
};

// 状態をファイルに保存
static void save_state(uint32_t next_mask, uint64_t total_eval_count, unsigned int initial_thread_count) {
    std::string filename;
    int len = WideCharToMultiByte(CP_UTF8, 0, kStateFile, -1, NULL, 0, NULL, NULL);
    if (len > 0) {
        filename.resize(len - 1);
        WideCharToMultiByte(CP_UTF8, 0, kStateFile, -1, &filename[0], len, NULL, NULL);
    }
    if (filename.empty()) return;

    std::ofstream ofs(filename, std::ios::binary);
    if (!ofs.is_open()) return;

    // 修正: initial_thread_count を含めて保存
    PersistenceData data = { next_mask, total_eval_count, initial_thread_count };
    ofs.write(reinterpret_cast<const char*>(&data), sizeof(data));

    // g_map (MAX_N + 1 バイト) を書き込む
    ofs.write(reinterpret_cast<const char*>(g_map.data()), g_map.size() * sizeof(g_map[0]));

    // g_expressions の書き込み (数式データ)
    for (size_t i = 0; i < g_expressions.size(); ++i) {
        const std::wstring& s = g_expressions[i];
        size_t len = s.length();
        ofs.write(reinterpret_cast<const char*>(&len), sizeof(len));
        if (ofs.fail()) return;

        if (len > 0) {
            ofs.write(reinterpret_cast<const char*>(s.data()), len * sizeof(wchar_t));
            if (ofs.fail()) return;
        }
    }
}

// 状態をファイルからロード
static bool load_state(uint32_t& next_mask, uint64_t& total_eval_count, unsigned int& initial_thread_count) {
    std::string filename;
    int len = WideCharToMultiByte(CP_UTF8, 0, kStateFile, -1, NULL, 0, NULL, NULL);
    if (len > 0) {
        filename.resize(len - 1);
        WideCharToMultiByte(CP_UTF8, 0, kStateFile, -1, &filename[0], len, NULL, NULL);
    }
    if (filename.empty()) return false;

    std::ifstream ifs(filename, std::ios::binary);
    if (!ifs.is_open()) return false;

    ifs.seekg(0, std::ios::end);
    long long file_size = ifs.tellg();
    if (file_size < (long long)sizeof(PersistenceData)) return false;
    ifs.seekg(0, std::ios::beg);

    PersistenceData data;
    ifs.read(reinterpret_cast<char*>(&data), sizeof(data));
    if (ifs.fail()) return false;

    // 修正: ロード時に初期スレッド数を取得
    next_mask = data.next_mask_start;
    total_eval_count = data.total_eval_count;
    initial_thread_count = data.initial_thread_count;

    // g_map (MAX_N + 1 バイト) を読み込む
    ifs.read(reinterpret_cast<char*>(g_map.data()), g_map.size() * sizeof(g_map[0]));
    if (ifs.fail()) return false;

    // g_expressions の読み込み (数式データ)
    for (size_t i = 0; i < g_expressions.size(); ++i) {
        size_t len = 0;

        // 1. 文字列長を読み込む
        ifs.read(reinterpret_cast<char*>(&len), sizeof(len));
        if (ifs.fail()) return false;

        // 2. 文字列データを読み込む
        if (len > 0) {
            g_expressions[i].resize(len);
            ifs.read(reinterpret_cast<char*>(&g_expressions[i][0]), len * sizeof(wchar_t));
            if (ifs.fail()) return false;
        }
        else {
            g_expressions[i].clear();
        }
    }

    if (ifs.fail() && !ifs.eof()) {
        return false;
    }

    return true;
}

// ----------------- Parallel Worker thread -------------------

struct ThreadData {
    HWND hWnd;
    bool useConcat;
    std::wstring opsSet;
    uint32_t maxTrees;
    uint32_t maskStart;
    uint32_t maskEnd;
    std::atomic<uint64_t>* globalEvalCount;
    size_t threadIndex; // g_current_expressions_by_thread のインデックス
};

// 並列ワーカープロシージャ
static DWORD WINAPI ParallelWorkerProc(LPVOID lp) {
    std::unique_ptr<ThreadData> u((ThreadData*)lp);
    g_active_thread_count.fetch_add(1);

    const int opsBase = (int)u->opsSet.size();

    for (uint32_t mask = u->maskStart; mask < u->maskEnd && !g_cancel.load(); ++mask) {

        // 進捗の更新
        if (mask > g_current_mask_processing.load()) {
            g_current_mask_processing.store(mask);
        }

        std::vector<std::wstring> operandsStr;
        build_operands((uint8_t)mask, operandsStr);
        // k は元のオペランドの数 (1〜9)
        const int k = (int)operandsStr.size();

        std::vector<std::unique_ptr<Node>> pos_leaves;
        // make_leaves は k 個の「正の」葉ノードを生成
        make_leaves(operandsStr, pos_leaves);

        // k <= 1 の場合、単一の葉ノードの結果をチェック
        if (k <= 1) {
            if (!pos_leaves.empty()) {
                BigRat v_rat = pos_leaves[0]->val;
                BigInt n_pos = v_rat.numerator();

                // 1. 正の値のチェック
                if (n_pos >= 1 && n_pos <= MAX_N) {
                    int v = 0;
                    try { v = std::stoi(n_pos.convert_to<std::string>()); }
                    catch (const std::exception&) {}

                    if (v >= 1 && v <= MAX_N) {
                        if (g_map[(size_t)v] == 0) {
                            g_map[(size_t)v] = 1;
                            g_expressions[(size_t)v] = pos_leaves[0]->text;
                        }
                    }
                }

                // 2. 負の値（単項マイナス）のチェック。結果の絶対値が 1..MAX_N に入るか
                BigInt n_neg = -n_pos;
                BigInt abs_n = (n_neg < 0) ? -n_neg : n_neg;

                if (abs_n >= 1 && abs_n <= MAX_N) {
                    int v = 0;
                    try { v = std::stoi(abs_n.convert_to<std::string>()); }
                    catch (const std::exception&) {}

                    if (v >= 1 && v <= MAX_N) {
                        std::wstring neg_text = L"(-" + pos_leaves[0]->text + L")";
                        if (g_map[(size_t)v] == 0) {
                            g_map[(size_t)v] = 1;
                            g_expressions[(size_t)v] = neg_text;
                        }
                    }
                }

                // 現在処理中の式を報告 (正の葉ノードの式)
                if (u->threadIndex < g_current_expressions_by_thread.size()) {
                    g_current_expressions_by_thread[u->threadIndex] = pos_leaves[0]->text;
                }
            }
            continue;
        }

        // k > 1 の場合
        std::vector<int> idx(k - 1, 0); // 演算子リストは k-1 個
        do {
            if (g_cancel.load()) goto end_mask_loop;

            // k-1 個の演算子を設定
            std::vector<wchar_t> ops_vec; ops_vec.resize(k - 1);
            for (int i = 0; i < k - 1; ++i) ops_vec[i] = u->opsSet[(size_t)idx[i]];

            std::vector<std::unique_ptr<Node>> base_trees;
            uint32_t budget = u->maxTrees;
            bool aborted = false;

            // k 個の正のオペランド (pos_leaves) と k-1 個の演算子でツリー構造を生成
            genTreesRec(0, k - 1, pos_leaves, ops_vec, base_trees, budget, aborted);

            if (g_cancel.load() || base_trees.empty()) {
                if (g_cancel.load()) goto end_mask_loop;
                continue;
            }

            // --- 単項マイナス（符号反転）の試行 ---
            // 2^k 通りの符号パターンを試す (k <= 9 なので 512 通り)
            for (uint32_t sign_mask = 0; sign_mask < (1u << k); ++sign_mask) {
                if (g_cancel.load()) goto end_mask_loop;

                for (auto& base_tree : base_trees) {
                    if (g_cancel.load()) goto end_mask_loop;

                    // base_tree のディープコピーを作成
                    auto current_tree = clone_node(base_tree);

                    // 葉ノードに符号を適用
                    std::function<void(Node*, uint32_t, int&)> apply_sign_rec =
                        [&](Node* n, uint32_t mask, int& leaf_idx) {
                        if (!n) return;
                        if (n->isLeaf) {
                            if (leaf_idx < k && (mask & (1u << leaf_idx))) { // 該当ビットが立っている場合、負にする
                                n->val = -n->val;
                                // テキストも更新 (例: 123 -> (-123))
                                n->text = L"(-" + n->text + L")";
                            }
                            leaf_idx++;
                            return;
                        }

                        apply_sign_rec(n->L.get(), mask, leaf_idx);
                        apply_sign_rec(n->R.get(), mask, leaf_idx);
                        };

                    int leaf_index = 0;
                    apply_sign_rec(current_tree.get(), sign_mask, leaf_index);


                    // 現在処理中の式を報告
                    if (u->threadIndex < g_current_expressions_by_thread.size()) {
                        g_current_expressions_by_thread[u->threadIndex] = current_tree->text;
                    }

                    // 評価とマーキング
                    std::vector<std::unique_ptr<Node>> single_tree_vec;
                    single_tree_vec.push_back(std::move(current_tree));
                    uint64_t evaluated_count = eval_and_mark(single_tree_vec, g_map);
                    u->globalEvalCount->fetch_add(evaluated_count);
                }
            }

        } while (nextOpVector(idx, opsBase) && !g_cancel.load());

    end_mask_loop:;
        if (g_cancel.load()) break;
    }

    // スレッド終了時にアクティブカウントを減らす
    g_active_thread_count.fetch_sub(1);
    return 0;
}

// UI更新とスレッド終了を監視するメインスレッドポーリング用のタイマープロシージャのプロトタイプ
static void CALLBACK TimerProc(HWND hWnd, UINT msg, UINT_PTR idEvent, DWORD dwTime);

// --------------- Rendering -----------------------
static void draw_bitmap(HWND hWnd, HDC hdc) {
    RECT rc; GetClientRect(hWnd, &rc);
    static const int panelH = 90;
    int W = rc.right - rc.left;
    int H = rc.bottom - rc.top - panelH;

    int dstW = W - 20;
    int dstH = H - 20;
    if (dstW < BMP_W) dstW = BMP_W;
    if (dstH < BMP_H) dstH = BMP_H;

    int x_start = 10;
    int y_start = panelH + 10;

    // 1. ビットマップ全体をストレッチ描画
    StretchDIBits(hdc,
        x_start, y_start, dstW, dstH,
        0, 0, BMP_W, BMP_H,
        g_pixels.data(), &g_bmi, DIB_RGB_COLORS, SRCCOPY);

    // 2. GDIで10958のセルに赤枠を描画

    const int target_n = 10958;
    int target_x_bmp, target_y_bmp;

    if (num_to_xy(target_n, target_x_bmp, target_y_bmp)) {
        double cell_w = (double)dstW / BMP_W;
        double cell_h = (double)dstH / BMP_H;

        int x1 = (int)std::round(x_start + target_x_bmp * cell_w);
        int y1 = (int)std::round(y_start + target_y_bmp * cell_h);
        int x2 = (int)std::round(x_start + (target_x_bmp + 1) * cell_w);
        int y2 = (int)std::round(y_start + (target_y_bmp + 1) * cell_h);

        HPEN hRedPen = CreatePen(PS_SOLID, 1, RGB(255, 0, 0));
        HPEN hOldPen = (HPEN)SelectObject(hdc, hRedPen);

        HBRUSH hOldBrush = (HBRUSH)SelectObject(hdc, GetStockObject(NULL_BRUSH));

        // Rectangle関数で枠を描画
        Rectangle(hdc, x1, y1, x2 + 1, y2 + 1);

        SelectObject(hdc, hOldBrush);
        SelectObject(hdc, hOldPen);
        DeleteObject(hRedPen);
    }
}

// --------------- Win32 UI -----------------------
struct GlobalStateContainer {
    std::atomic<uint64_t>* globalEvalCountPtr = nullptr;
    uint32_t maskStartFrom = 0; // 途中再開用の開始マスク値
    uint32_t totalMasks = 0;    // 総マスク数
    unsigned int initialThreadCount = 0; // 初回論理コア数を保持
};

static LRESULT CALLBACK WndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    GlobalStateContainer* container = (GlobalStateContainer*)GetWindowLongPtrW(hWnd, GWLP_USERDATA);

    switch (msg) {
    case WM_CREATE: {
        // init bitmap buffers (最大値で初期化)
        g_map.assign(MAX_N + 1, 0);
        g_pixels.assign(BMP_W * BMP_H, 0xFF202020);
        g_expressions.assign(MAX_N + 1, L"");

        GlobalStateContainer* new_container = new GlobalStateContainer();
        SetWindowLongPtrW(hWnd, GWLP_USERDATA, (LONG_PTR)new_container);

        // 修正: 論理コア数をコンテナに保存
        new_container->initialThreadCount = s_initial_thread_count;

        // ロード処理の試行
        uint32_t loaded_mask = 0;
        uint64_t loaded_eval_count = 0;
        unsigned int loaded_thread_count = 0;

        // 修正: load_state でスレッド数も読み込む
        bool loaded = load_state(loaded_mask, loaded_eval_count, loaded_thread_count);

        // ロードしたマスク値をコンテナに保存
        if (loaded) {
            new_container->maskStartFrom = loaded_mask;
            // ロードしたスレッド数を優先（ただし、0や非現実的な値は現在の論理コア数にフォールバック）
            if (loaded_thread_count > 0 && loaded_thread_count <= 256) {
                new_container->initialThreadCount = loaded_thread_count;
            }
            set_status(hWnd, L"State loaded. Ready to resume calculation.");
            refresh_pixels(); // ロードしたg_mapを反映
        }
        else {
            new_container->maskStartFrom = 0;
        }

        ZeroMemory(&g_bmi, sizeof(g_bmi));
        g_bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
        g_bmi.bmiHeader.biWidth = BMP_W;
        g_bmi.bmiHeader.biHeight = -BMP_H;
        g_bmi.bmiHeader.biPlanes = 1;
        g_bmi.bmiHeader.biBitCount = 32;
        g_bmi.bmiHeader.biCompression = BI_RGB;

        int y = 0;
        // 1行目: ボタンと設定
        CreateWindowW(L"BUTTON", L"Start", WS_CHILD | WS_VISIBLE, 10, y + 10, 80, 24, hWnd, (HMENU)IDC_START, 0, 0);
        CreateWindowW(L"BUTTON", L"Cancel", WS_CHILD | WS_VISIBLE | WS_DISABLED, 100, y + 10, 80, 24, hWnd, (HMENU)IDC_CANCEL, 0, 0);

        CreateWindowW(L"BUTTON", L"Concatenation (12, 123 ...)", WS_CHILD | WS_VISIBLE | BS_AUTOCHECKBOX,
            200, y + 10, 220, 24, hWnd, (HMENU)IDC_CONCAT_CHECK, 0, 0);
        SendMessageW(GetDlgItem(hWnd, IDC_CONCAT_CHECK), BM_SETCHECK, kDefaultConcatOn ? BST_CHECKED : BST_UNCHECKED, 0);

        CreateWindowW(L"STATIC", L"Ops (+-*/^):", WS_CHILD | WS_VISIBLE, 440, y + 10 + 3, 90, 18, hWnd, 0, 0, 0);
        CreateWindowW(L"EDIT", kDefaultOps, WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
            530, y + 10, 100, 24, hWnd, (HMENU)IDC_OPS_EDIT, 0, 0);

        // Max Masks / Max Trees の入力枠は削除されました。

        // 2行目: マウスオーバー/現在処理中の式情報を表示
        CreateWindowW(L"STATIC", L"Cursor Info:", WS_CHILD | WS_VISIBLE,
            10, y + 40, 90, 18, hWnd, 0, 0, 0);
        CreateWindowW(L"STATIC", L"Ready.", WS_CHILD | WS_VISIBLE | WS_BORDER | ES_READONLY,
            100, y + 40, 920, 18, hWnd, (HMENU)IDC_CURRENT_EXPR, 0, 0);

        // 3行目: Status (y=65)
        CreateWindowW(L"STATIC", L"Status:", WS_CHILD | WS_VISIBLE,
            10, y + 65, 90, 18, hWnd, 0, 0, 0);
        CreateWindowW(L"STATIC", L"Ready.", WS_CHILD | WS_VISIBLE,
            100, y + 65, 920, 18, hWnd, (HMENU)IDC_STATUS, 0, 0);

        SetTimer(hWnd, IDT_REPAINT, 150, (TIMERPROC)TimerProc);

        // UIの初期状態を反映
        if (loaded) {
            wchar_t status_buf[256];
            _snwprintf(status_buf, 256, L"State loaded. Mask start: %u. Eval count: %llu | threads=%u | dots=%u",
                loaded_mask, (unsigned long long)loaded_eval_count, new_container->initialThreadCount,
                (unsigned)std::count(g_map.begin(), g_map.end(), (uint8_t)1));
            set_status(hWnd, status_buf);
        }

        return 0;
    }
    case WM_COMMAND: {
        switch (LOWORD(wParam)) {
        case IDC_START: {
            if (g_running.load()) break;
            g_cancel = false;
            g_running = true;

            EnableWindow(GetDlgItem(hWnd, IDC_START), FALSE);
            EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), TRUE);
            set_status(hWnd, L"Starting parallel enumeration (Stable Mode)...");

            struct Args {
                bool useConcat;
                std::wstring opsSet;
                uint32_t maxMasks;
                uint32_t maxTrees;
            } temp_args;

            temp_args.useConcat = (SendMessageW(GetDlgItem(hWnd, IDC_CONCAT_CHECK), BM_GETCHECK, 0, 0) == BST_CHECKED);

            std::wstring ops; ops.resize(256);
            int n = GetWindowTextW(GetDlgItem(hWnd, IDC_OPS_EDIT), &ops[0], 256);
            ops.resize((n > 0) ? n : 0);
            std::wstring clean;
            for (wchar_t c : ops) {
                if (c == L'+' || c == L'-' || c == L'*' || c == L'/' || c == L'^') clean.push_back(c);
            }
            if (clean.empty()) clean = kDefaultOps;
            temp_args.opsSet = clean;

            // 固定値を使用
            temp_args.maxMasks = kDefaultMaxMasks;
            temp_args.maxTrees = kDefaultMaxTrees;

            // GlobalStateContainerを再取得
            container = (GlobalStateContainer*)GetWindowLongPtrW(hWnd, GWLP_USERDATA);

            uint32_t maskBegin = 0, maskEnd = temp_args.useConcat ? 256u : 1u;
            // 固定値のkDefaultMaxMasksを使用
            if (kDefaultMaxMasks < (maskEnd - maskBegin)) maskEnd = maskBegin + kDefaultMaxMasks;

            // ロードされた値(container->maskStartFrom)を優先して開始マスクを決定
            uint32_t actual_mask_start = container->maskStartFrom;

            if (actual_mask_start >= maskEnd) {
                actual_mask_start = 0;
            }

            static std::atomic<uint64_t> s_globalEvalCount{ 0 };
            s_globalEvalCount = 0;

            unsigned int saved_thread_count = container->initialThreadCount;

            // ロードされたマスクから開始する場合は、再度状態をロードして評価カウントとマップを初期化
            if (actual_mask_start != 0) {
                uint32_t temp_loaded_mask = 0;
                uint64_t temp_loaded_eval_count = 0;
                unsigned int temp_loaded_thread_count = 0;

                if (load_state(temp_loaded_mask, temp_loaded_eval_count, temp_loaded_thread_count)) {
                    s_globalEvalCount = temp_loaded_eval_count;
                    g_current_mask_processing.store(actual_mask_start);

                    // 修正: ロードしたスレッド数を優先して利用
                    if (temp_loaded_thread_count > 0 && temp_loaded_thread_count <= 256) {
                        saved_thread_count = temp_loaded_thread_count;
                        container->initialThreadCount = saved_thread_count; // コンテナにも反映
                    }

                    set_status(hWnd, L"Resuming parallel enumeration...");
                }
                else {
                    // ロード失敗: 状態をリセットして最初から
                    actual_mask_start = 0;
                    container->maskStartFrom = 0;
                    std::fill(g_map.begin(), g_map.end(), 0);
                    std::fill(g_expressions.begin(), g_expressions.end(), L"");
                    g_current_mask_processing.store(0);
                }
            }
            else {
                // 最初から開始する場合、マップと式を初期化
                container->maskStartFrom = 0;
                std::fill(g_map.begin(), g_map.end(), 0);
                std::fill(g_expressions.begin(), g_expressions.end(), L"");
                g_current_mask_processing.store(0);
            }

            // 修正されたタスク分割ロジックの開始
            uint32_t remaining_masks = maskEnd - actual_mask_start;
            container->totalMasks = maskEnd;

            // 修正: スレッド数を、保存された論理コア数を最大として利用
            unsigned int max_cores = saved_thread_count;
            if (max_cores == 0) max_cores = s_initial_thread_count; // フォールバック

            unsigned int num_threads = max_cores;

            // 実行するスレッド数は、残りのマスク数を超えないように調整
            if (remaining_masks < num_threads) {
                num_threads = remaining_masks;
                // タスクが残っている場合は、最低1スレッドを保証
                if (num_threads == 0 && remaining_masks > 0) num_threads = 1;
            }

            if (num_threads == 0) {
                // タスクがない場合はスレッドを起動しない
                g_running = false;
                EnableWindow(GetDlgItem(hWnd, IDC_START), TRUE);
                EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), FALSE);
                set_status(hWnd, L"Enumeration already complete or range invalid.");
                return 0;
            }

            // スレッドごとの式追跡コンテナを初期化
            g_current_expressions_by_thread.assign(num_threads, L"");

            uint32_t masks_per_thread = remaining_masks / num_threads;
            uint32_t remainder = remaining_masks % num_threads;

            g_hWorkers.clear();
            g_hWorkers.reserve(num_threads);

            uint32_t current_start = actual_mask_start;
            bool success = true;

            container->globalEvalCountPtr = &s_globalEvalCount;

            // 修正: ここで実際に使用するスレッド数 (num_threads) をコンテナに保存し直す
            container->initialThreadCount = num_threads;

            for (unsigned int i = 0; i < num_threads; ++i) {
                uint32_t count = masks_per_thread + (i < remainder ? 1 : 0);
                uint32_t current_end = current_start + count;

                // タスクが割り当てられたスレッドのみ起動 (count > 0)
                if (count > 0) {
                    ThreadData* args = new ThreadData();
                    args->hWnd = hWnd;
                    args->useConcat = temp_args.useConcat;
                    args->opsSet = temp_args.opsSet;
                    args->maxTrees = kDefaultMaxTrees; // 固定値を使用
                    args->maskStart = current_start;
                    args->maskEnd = current_end;
                    args->globalEvalCount = &s_globalEvalCount;
                    args->threadIndex = i; // インデックスを割り当て

                    DWORD tid = 0;
                    HANDLE hThread = CreateThread(nullptr, 0, ParallelWorkerProc, args, 0, &tid);

                    if (hThread) {
                        g_hWorkers.push_back(hThread);
                        SetThreadPriority(hThread, THREAD_PRIORITY_HIGHEST);
                    }
                    else {
                        delete args;
                        success = false;
                        break;
                    }
                }

                current_start = current_end;
            }

            if (!success) {
                g_cancel = true;
                for (HANDLE h : g_hWorkers) {
                    if (h) WaitForSingleObject(h, INFINITE);
                    if (h) CloseHandle(h);
                }
                g_hWorkers.clear();

                g_running = false;
                MessageBoxW(hWnd, L"Failed to create some worker threads. Aborting.", L"Error", MB_ICONERROR);
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
    case WM_TIMER: {
        if (wParam == IDT_REPAINT) {
            TimerProc(hWnd, msg, wParam, lParam);
            return 0;
        }
        break;
    }
    case WM_MOUSEMOVE: {
        int mouseX = GET_X_LPARAM(lParam);
        int mouseY = GET_Y_LPARAM(lParam);

        RECT rc; GetClientRect(hWnd, &rc);
        static const int panelH = 90;
        int W = rc.right - rc.left;
        int H = rc.bottom - rc.top - panelH;

        int dstW = W - 20;
        int dstH = H - 20;
        if (dstW < BMP_W) dstW = BMP_W;
        if (dstH < BMP_H) dstH = BMP_H;

        int x_start = 10;
        int y_start = panelH + 10;

        int relativeX = mouseX - x_start;
        int relativeY = mouseY - y_start;

        if (relativeX >= 0 && relativeX < dstW && relativeY >= 0 && relativeY < dstH) {
            int bmp_x = (int)((double)relativeX * BMP_W / dstW);
            int bmp_y = (int)((double)relativeY * BMP_H / dstH);

            int index = bmp_y * BMP_W + bmp_x;
            int n = index + 1;

            if (n >= 1 && n <= MAX_N) {
                if (g_map[(size_t)n] == 1) {
                    std::wstring expr = g_expressions[(size_t)n];
                    if (expr.empty()) expr = L"Formula not recorded (Restarted or max masks exceeded)";

                    wchar_t buf[512];
                    _snwprintf(buf, 512, L"Value: %d | Expression: %s", n, expr.c_str());
                    set_current_expr(hWnd, buf);
                }
                else {
                    wchar_t buf[256];
                    _snwprintf(buf, 256, L"Value: %d | Status: Not found yet.", n);
                    set_current_expr(hWnd, buf);
                }
            }
            else {
                set_current_expr(hWnd, L"Ready.");
            }
        }
        else if (g_running.load()) {
            // 計算中は、マウスオーバー情報がない場合、現在の計算式を表示
            if (g_active_thread_count.load() > 0 && !g_current_expressions_by_thread.empty() && !g_current_expressions_by_thread[0].empty()) {
                wchar_t buf[1024];
                _snwprintf(buf, 1024, L"Computing: %s (Mask %u)",
                    g_current_expressions_by_thread[0].c_str(), g_current_mask_processing.load());
                set_current_expr(hWnd, buf);
            }
        }
        else {
            set_current_expr(hWnd, L"Ready.");
        }
        return 0;
    }
    case WM_CLOSE: {
        if (g_running.load()) {
            if (IDYES == MessageBoxW(hWnd, L"Enumeration is running. Save and exit?", L"Confirm", MB_YESNO | MB_ICONQUESTION)) {
                g_cancel = true;
                // TimerProcにクリーンアップを任せる
                DestroyWindow(hWnd);
            }
            return 0;
        }
        DestroyWindow(hWnd);
        return 0;
    }
    case WM_DESTROY: {
        KillTimer(hWnd, IDT_REPAINT);

        container = (GlobalStateContainer*)GetWindowLongPtrW(hWnd, GWLP_USERDATA);
        if (container) {
            for (HANDLE h : g_hWorkers) {
                if (h) CloseHandle(h);
            }
            g_hWorkers.clear();

            delete container;
            SetWindowLongPtrW(hWnd, GWLP_USERDATA, 0);
        }

        PostQuitMessage(0);
        return 0;
    }
    }
    return DefWindowProcW(hWnd, msg, wParam, lParam);
}

// UI更新とスレッド終了を監視するメインスレッドポーリング用のタイマープロシージャの実現
static void CALLBACK TimerProc(HWND hWnd, UINT msg, UINT_PTR idEvent, DWORD dwTime) {
    UNREFERENCED_PARAMETER(msg);
    UNREFERENCED_PARAMETER(idEvent);
    UNREFERENCED_PARAMETER(dwTime);

    if (g_running.load()) {
        bool all_finished = true;

        // 終了したスレッドをクローズし、アクティブなスレッドを更新
        std::vector<HANDLE> active_workers;
        for (HANDLE h : g_hWorkers) {
            if (WaitForSingleObject(h, 0) == WAIT_TIMEOUT) {
                active_workers.push_back(h);
                all_finished = false;
            }
            else {
                CloseHandle(h); // 終了したスレッドのハンドルをクローズ
            }
        }
        g_hWorkers = active_workers; // アクティブなスレッドリストに更新

        GlobalStateContainer* container = (GlobalStateContainer*)GetWindowLongPtrW(hWnd, GWLP_USERDATA);
        uint64_t currentEvalCount = 0;
        if (container && container->globalEvalCountPtr) {
            currentEvalCount = container->globalEvalCountPtr->load();
        }
        uint32_t currentMask = g_current_mask_processing.load();
        uint32_t totalMasks = container->totalMasks;
        uint32_t initialStartMask = container->maskStartFrom;

        // 定期保存の処理
        auto now = std::chrono::steady_clock::now();
        if (std::chrono::duration_cast<std::chrono::milliseconds>(now - g_last_save_time).count() > kSaveIntervalMs) {
            // 修正: TimerProcでも初期スレッド数を保存
            save_state(currentMask, currentEvalCount, container->initialThreadCount);
            g_last_save_time = now;
        }

        // 終了判定ロジック
        // currentMask は最後に処理を開始したマスクなので、totalMasks に到達した時点で完了とみなす
        bool finished_progress = (currentMask >= totalMasks);

        if (all_finished && (g_cancel.load() || finished_progress)) {
            if (g_running.load()) {
                g_running = false;

                g_hWorkers.clear();

                refresh_pixels();
                InvalidateRect(hWnd, nullptr, FALSE);

                // 終了時の保存/削除
                if (finished_progress && !g_cancel.load()) {
                    // 全て完了: 保存ファイルを削除
                    std::string filename;
                    int len = WideCharToMultiByte(CP_UTF8, 0, kStateFile, -1, NULL, 0, NULL, NULL);
                    if (len > 0) {
                        filename.resize(len - 1);
                        WideCharToMultiByte(CP_UTF8, 0, kStateFile, -1, &filename[0], len, NULL, NULL);
                        std::remove(filename.c_str());
                    }
                    container->maskStartFrom = totalMasks; // 完了マーク
                }
                else {
                    // キャンセル完了、または途中のタスク完了（ファイルは保持）
                    // 修正: 終了時にも初期スレッド数を保存
                    save_state(currentMask, currentEvalCount, container->initialThreadCount);
                    container->maskStartFrom = currentMask;
                }

                wchar_t fin[256];
                _snwprintf(fin, 256, L"%s. trees(eval)≈ %llu | dots=%u",
                    finished_progress ? L"Finished" : L"Cancelled and Saved",
                    (unsigned long long)currentEvalCount,
                    (unsigned)std::count(g_map.begin(), g_map.end(), (uint8_t)1));
                set_status(hWnd, fin);

                g_cancel.store(false);
                EnableWindow(GetDlgItem(hWnd, IDC_START), TRUE);
                EnableWindow(GetDlgItem(hWnd, IDC_CANCEL), FALSE);
            }
            return;
        }

        refresh_pixels();
        RedrawWindow(hWnd, nullptr, nullptr, RDW_INVALIDATE | RDW_UPDATENOW);

        // 計算中の式をUIに表示
        if (g_active_thread_count.load() > 0 && !g_current_expressions_by_thread.empty() && !g_current_expressions_by_thread[0].empty()) {
            wchar_t expr_buf[1024];
            _snwprintf(expr_buf, 1024, L"Computing: %s (Mask %u)",
                g_current_expressions_by_thread[0].c_str(), currentMask);
            SetWindowTextW(GetDlgItem(hWnd, IDC_CURRENT_EXPR), expr_buf);
        }

        wchar_t buf[256];
        uint32_t maskRange = totalMasks - initialStartMask;
        uint32_t progress = (maskRange > 0) ? (currentMask - initialStartMask) * 100 / maskRange : 0;
        if (progress > 100) progress = 100;

        _snwprintf(buf, 256, L"Working... | Progress: %u%% | Mask: %u/%u | threads=%u | trees(eval)≈ %llu | dots=%u",
            progress,
            currentMask, totalMasks,
            (unsigned)g_hWorkers.size(), // アクティブなスレッド数
            (unsigned long long)currentEvalCount,
            (unsigned)std::count(g_map.begin(), g_map.end(), (uint8_t)1));
        set_status(hWnd, buf);
    }
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

    HWND hWnd = CreateWindowW(cls, L"1..9 Expressions → 1..11111 Dot Map (Persistence Mode)",
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