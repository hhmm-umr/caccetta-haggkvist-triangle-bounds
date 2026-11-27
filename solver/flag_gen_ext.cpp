// flag_gen_ext.cpp - Exact integer generator for Class 3 (Generalized Induction, linear + SOS-weighted)
// and Class 4 (Pointwise & SOS-weighted CSS/CKLS) constraints on top of flags_m<m>.bin!
//
// Reads canonical models M_m directly from flags_m<m>.bin (guaranteeing 100% identical model indexing!),
// computes exact integer numerator tables + exact denominators for:
//   1. Linear Induction constraints (all sink types k=1..m-1 + all lifted non-sink types k=2..m-2):
//        f(sigma) = s*(sigma) + c * (F0(sigma) - 1_sigma) >= 0, multiplied by all F in F^tau_{m-1}
//        (where tau = sigma for sink, tau = sigma+ = F0(sigma) for non-sink).
//        Stored as exact integer triplets for (S_star, F0, One) with common denominator!
//   2. Linear CSS/CKLS constraints (all sink types k=1..m-2 + all lifted non-sink types k=2..m-3):
//        g_CSS(sigma, r) = alpha*chi(sigma) + 2r*s*(sigma) + (r^2 - 2cr)*1_sigma >= 0,
//        multiplied by all F in F^tau_{m-2}.
//        Stored as exact integer triplets for (Chi, S_star, One) with common denominator!
//   3. SOS-weighted Induction PSD blocks [[f(sigma) * h_a * h_b]]_tau (tau = sigma or sigma+):
//        m=4: k=1 (lam, ell=2, 3x3)
//        m=5: k=1 (lam, ell=2, 3x3), k=2 (beta, ell=3, 8x8)
//        m=6: k=1 (lam, ell=3, 14x14), k=3 (T, ell=4, 20x20 for f(T) and pi(f(beta))),
//             k=3 (V, ell=4, 22x22 for f(V) and pi(f(beta_bar)))
//   4. SOS-weighted CSS PSD blocks [[g_CSS(sigma, r) * h_a * h_b]]_sigma:
//        m=5: k=1 (lam, ell=2, 3x3)
//        m=6: k=2 (beta, ell=3, 8x8)
//
// Compile: g++ -O3 -march=native -fopenmp flag_gen_ext.cpp -o flag_gen_ext

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

using u64 = uint64_t;
using u8 = uint8_t;

struct AdjMat {
    int n;
    u8 a[8][8];
};

static inline AdjMat decode_graph(int n, u64 code) {
    AdjMat g;
    g.n = n;
    memset(g.a, 0, sizeof(g.a));
    int idx = 0;
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            u64 v = (code >> (2 * idx)) & 3ULL;
            if (v == 1) g.a[i][j] = 1;
            else if (v == 2) g.a[j][i] = 1;
            ++idx;
        }
    }
    return g;
}

static inline u64 encode_graph(const AdjMat &g) {
    u64 code = 0;
    int idx = 0;
    for (int i = 0; i < g.n; ++i) {
        for (int j = i + 1; j < g.n; ++j) {
            u64 v = 0;
            if (g.a[i][j]) v = 1;
            else if (g.a[j][i]) v = 2;
            code |= (v << (2 * idx));
            ++idx;
        }
    }
    return code;
}

static inline u64 encode_permuted(const AdjMat &g, const int *perm) {
    u64 code = 0;
    int idx = 0;
    for (int i = 0; i < g.n; ++i) {
        int ui = perm[i];
        for (int j = i + 1; j < g.n; ++j) {
            int uj = perm[j];
            u64 v = 0;
            if (g.a[ui][uj]) v = 1;
            else if (g.a[uj][ui]) v = 2;
            code |= (v << (2 * idx));
            ++idx;
        }
    }
    return code;
}

static inline bool has_c3_with_last(const AdjMat &g) {
    int last = g.n - 1;
    for (int i = 0; i < last; ++i) {
        if (g.a[last][i]) {
            for (int j = 0; j < last; ++j) {
                if (g.a[i][j] && g.a[j][last]) return true;
            }
        }
    }
    return false;
}

static inline u64 canonical_flag_exact(const AdjMat &g, int k) {
    int n = g.n;
    int m = n - k;
    int perm[8];
    for (int i = 0; i < n; ++i) perm[i] = i;
    if (m <= 1) return encode_graph(g);
    assert(m <= 6);
    u64 best = ~0ULL;
    do {
        u64 c = encode_permuted(g, perm);
        if (c < best) best = c;
    } while (std::next_permutation(perm + k, perm + n));
    return best;
}

static inline AdjMat induce(const AdjMat &H, const int *verts, int sz) {
    AdjMat sub;
    sub.n = sz;
    for (int i = 0; i < sz; ++i) {
        int ui = verts[i];
        for (int j = 0; j < sz; ++j) sub.a[i][j] = H.a[ui][verts[j]];
    }
    return sub;
}

static long long factorial(int n) {
    long long r = 1;
    for (int i = 2; i <= n; ++i) r *= i;
    return r;
}

static std::vector<std::vector<u64>> generate_models(int max_n) {
    std::vector<std::vector<u64>> models(max_n + 1);
    models[0] = {0ULL};
    models[1] = {0ULL};
    for (int n = 2; n <= max_n; ++n) {
        std::vector<u64> cand;
        int p3 = 1;
        for (int i = 0; i < n - 1; ++i) p3 *= 3;
        for (u64 base_c : models[n - 1]) {
            AdjMat base = decode_graph(n - 1, base_c);
            AdjMat g;
            g.n = n;
            for (int mask = 0; mask < p3; ++mask) {
                memcpy(g.a, base.a, sizeof(base.a));
                for (int i = 0; i < n; ++i) g.a[i][n - 1] = g.a[n - 1][i] = 0;
                int x = mask;
                for (int i = 0; i < n - 1; ++i) {
                    int s = x % 3; x /= 3;
                    if (s == 1) g.a[i][n - 1] = 1;
                    else if (s == 2) g.a[n - 1][i] = 1;
                }
                if (!has_c3_with_last(g)) cand.push_back(canonical_flag_exact(g, 0));
            }
        }
        std::sort(cand.begin(), cand.end());
        cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
        models[n] = std::move(cand);
    }
    return models;
}

static std::vector<u64> generate_flags(int k, u64 sigma_code, int ell) {
    std::vector<u64> cur = {sigma_code};
    for (int n = k + 1; n <= ell; ++n) {
        std::vector<u64> next;
        int p3 = 1;
        for (int i = 0; i < n - 1; ++i) p3 *= 3;
        for (u64 code : cur) {
            AdjMat base = decode_graph(n - 1, code);
            AdjMat g;
            g.n = n;
            for (int mask = 0; mask < p3; ++mask) {
                memcpy(g.a, base.a, sizeof(base.a));
                for (int i = 0; i < n; ++i) g.a[i][n - 1] = g.a[n - 1][i] = 0;
                int x = mask;
                for (int i = 0; i < n - 1; ++i) {
                    int s = x % 3; x /= 3;
                    if (s == 1) g.a[i][n - 1] = 1;
                    else if (s == 2) g.a[n - 1][i] = 1;
                }
                if (!has_c3_with_last(g)) next.push_back(canonical_flag_exact(g, k));
            }
        }
        std::sort(next.begin(), next.end());
        next.erase(std::unique(next.begin(), next.end()), next.end());
        cur = std::move(next);
    }
    return cur;
}

static bool has_sink_root(int k, u64 sigma_code) {
    AdjMat g = decode_graph(k, sigma_code);
    for (int r = 0; r < k; ++r) {
        bool ok = true;
        for (int i = 0; i < k; ++i) {
            if (i != r && !g.a[i][r]) { ok = false; break; }
        }
        if (ok) return true;
    }
    return false;
}

// Construct tau = F0(sigma) on k+1 vertices (vertices 0..k-1 induce sigma, vertex k has i -> k for all i < k)
static u64 lift_f0_type(int k, u64 sigma_code) {
    AdjMat g = decode_graph(k, sigma_code);
    g.n = k + 1;
    for (int i = 0; i < k + 1; ++i) g.a[i][k] = g.a[k][i] = 0;
    for (int i = 0; i < k; ++i) g.a[i][k] = 1;
    return encode_graph(g);
}

// Compute automorphism group of tau (size k_tau) acting on flags of size ell,
// preserving the subset {0..k_orig-1} (Wait: for lifted non-sink pi^{tau, [k]}(f(sigma)),
// any aut of tau preserving the subset {0..k_orig-1} ALSO preserves f(sigma)!).
static std::vector<std::vector<int>> compute_aut_action_preserving_prefix(
    int k_tau, u64 tau_code, int k_orig, int ell, const std::vector<u64> &flags
) {
    AdjMat sig = decode_graph(k_tau, tau_code);
    std::unordered_map<u64, int> fidx;
    for (size_t i = 0; i < flags.size(); ++i) fidx[flags[i]] = (int)i;

    std::vector<std::vector<int>> actions;
    int p[8];
    for (int i = 0; i < k_tau; ++i) p[i] = i;
    do {
        // Must preserve prefix set {0..k_orig-1}
        bool pres = true;
        for (int i = 0; i < k_orig; ++i) if (p[i] >= k_orig) { pres = false; break; }
        if (!pres) continue;
        if (encode_permuted(sig, p) != tau_code) continue;

        std::vector<int> act(flags.size());
        int fullp[8];
        for (int i = 0; i < k_tau; ++i) fullp[i] = p[i];
        for (int i = k_tau; i < ell; ++i) fullp[i] = i;
        for (size_t fi = 0; fi < flags.size(); ++fi) {
            AdjMat f = decode_graph(ell, flags[fi]);
            AdjMat pf;
            pf.n = ell;
            memset(pf.a, 0, sizeof(pf.a));
            for (int i = 0; i < ell; ++i)
                for (int j = 0; j < ell; ++j)
                    pf.a[i][j] = f.a[fullp[i]][fullp[j]];
            act[fi] = fidx.at(canonical_flag_exact(pf, k_tau));
        }
        actions.push_back(std::move(act));
    } while (std::next_permutation(p, p + k_tau));
    return actions;
}

static std::vector<std::array<int, 8>> make_injections(int m, int k) {
    std::vector<std::array<int, 8>> res;
    std::vector<int> comb(m, 0);
    std::fill(comb.end() - k, comb.end(), 1);
    do {
        int sel[8], cs = 0;
        for (int i = 0; i < m; ++i) if (comb[i]) sel[cs++] = i;
        do {
            std::array<int, 8> arr{};
            for (int i = 0; i < k; ++i) arr[i] = sel[i];
            res.push_back(arr);
        } while (std::next_permutation(sel, sel + k));
    } while (std::next_permutation(comb.begin(), comb.end()));
    return res;
}

struct LinTrip { int32_t h, f, c_sstar, c_f0, c_one; };
struct CssTrip { int32_t h, f, c_chi, c_sstar, c_one; };
struct PsdTrip { int32_t h, a, b, c0, c1, c2; }; // (sstar, f0, one) or (chi, sstar, one)

static void w_i32(std::ofstream &f, int32_t v) { f.write((const char *)&v, 4); }
static void w_i64(std::ofstream &f, int64_t v) { f.write((const char *)&v, 8); }
static void w_u64(std::ofstream &f, u64 v) { f.write((const char *)&v, 8); }

// 1. Compute exact linear Induction table for (tau_k, tau_code) with active prefix k_orig (<= tau_k),
//    multiplied by all F in F^{tau}_{ell_mult} where ell_mult = m - 1!
//    For each injection inj[0..tau_k-1] inducing tau in H, and each choice of 1 free vertex x in rem:
//    the remaining (m - 1 - tau_k) vertices form F!
//    Exact denominator = m! / (m - 1 - tau_k)! = (m)_{tau_k} * (m - tau_k) = (m)_{tau_k + 1}!
//    Wait: check! Choosing ordered inj[0..tau_k-1] ((m)_{tau_k} ways), then 1 vertex x from remaining
//    (m - tau_k ways), then the rest is a SINGLE unordered set of size (m - 1 - tau_k)!
//    Total choices per H = (m)_{tau_k + 1} = m! / (m - tau_k - 1)!.
//    For each choice (inj, x):
//      - One: always +1 (counts [[F]]_tau * 1 = [[F]]_tau!)
//      - F0:  +1 iff for all i < k_orig, H.a[inj[i]][x] == 1
//      - S*:  +1 iff (for all i < k_orig, H.a[x][inj[i]] == 0) AND NOT F0!
//    Check: sum_F (One(H, F) / denom) = p_ordered(tau, H), and for each F,
//      (S*(H, F) + c * (F0(H, F) - One(H, F))) / denom == [[f_orig * F]]_tau(H) EXACTLY!
static void compute_linear_ind_family(
    int m, const std::vector<u64> &models_m,
    int tau_k, u64 tau_code, int k_orig,
    std::vector<u64> &out_flags, long long &out_denom, std::vector<LinTrip> &out_trips
) {
    int ell_mult = m - 1;
    assert(tau_k <= ell_mult);
    out_flags = generate_flags(tau_k, tau_code, ell_mult);
    std::unordered_map<u64, int> fidx;
    for (size_t i = 0; i < out_flags.size(); ++i) fidx[out_flags[i]] = (int)i;

    out_denom = factorial(m) / factorial(m - tau_k - 1);
    auto injections = make_injections(m, tau_k);

    int nM = (int)models_m.size();
    std::vector<std::vector<LinTrip>> per_h(nM);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int hi = 0; hi < nM; ++hi) {
        AdjMat H = decode_graph(m, models_m[hi]);
        std::unordered_map<int, std::array<int, 3>> acc; // f -> {sstar, f0, one}
        for (const auto &inj : injections) {
            if (encode_graph(induce(H, inj.data(), tau_k)) != tau_code) continue;
            bool used[8] = {false};
            for (int i = 0; i < tau_k; ++i) used[inj[i]] = true;
            int rem[8], rc = 0;
            for (int i = 0; i < m; ++i) if (!used[i]) rem[rc++] = i;
            // rc == m - tau_k >= 1
            for (int xi = 0; xi < rc; ++xi) {
                int x = rem[xi];
                // Build F on inj[0..tau_k-1] union (rem \ {x})
                int vf[8], cf = tau_k;
                for (int i = 0; i < tau_k; ++i) vf[i] = inj[i];
                for (int j = 0; j < rc; ++j) if (j != xi) vf[cf++] = rem[j];
                int f = fidx.at(canonical_flag_exact(induce(H, vf, ell_mult), tau_k));

                bool all_in = true, no_out = true;
                for (int i = 0; i < k_orig; ++i) {
                    if (!H.a[inj[i]][x]) all_in = false;
                    if (H.a[x][inj[i]]) no_out = false;
                }
                auto &slot = acc[f];
                slot[2] += 1; // One
                if (all_in) slot[1] += 1; // F0
                else if (no_out) slot[0] += 1; // S*
            }
        }
        auto &vec = per_h[hi];
        vec.reserve(acc.size());
        for (auto &kv : acc) {
            vec.push_back({hi, kv.first, kv.second[0], kv.second[1], kv.second[2]});
        }
        std::sort(vec.begin(), vec.end(), [](const LinTrip &x, const LinTrip &y) { return x.f < y.f; });
    }
    out_trips.clear();
    for (int hi = 0; hi < nM; ++hi) out_trips.insert(out_trips.end(), per_h[hi].begin(), per_h[hi].end());
}

// 2. Compute exact linear CSS table for (tau_k, tau_code) with active prefix k_orig (<= tau_k),
//    multiplied by all F in F^{tau}_{m-2}!
//    Requires tau_k <= m - 2.
//    Choose ordered inj[0..tau_k-1] inducing tau, then ORDERED pair (x, y) from rem (rc*(rc-1) ways!),
//    remaining (m - 2 - tau_k) vertices form F!
//    Wait: check denominator!
//    Ordered inj: (m)_{tau_k}. Ordered (x, y) from (m - tau_k): (m - tau_k)*(m - tau_k - 1).
//    Total = (m)_{tau_k + 2} = m! / (m - tau_k - 2)!.
//    For each (inj, x, y):
//      - One: always +1
//      - S* (on x!): +1 iff (no_out(x) and not all_in(x))
//        (Check: averaging over ordered (x, y) gives EXACTLY [[s*(sigma) * F]]_tau!)
//      - Chi (on x, y!): +1 iff all_in(x) && all_in(y) && !H.a[x][y] && !H.a[y][x]!
//        (Check: matches ordered i.i.d. pair (x, y) with x, y in U and x not~ y!)
static void compute_linear_css_family(
    int m, const std::vector<u64> &models_m,
    int tau_k, u64 tau_code, int k_orig,
    std::vector<u64> &out_flags, long long &out_denom, std::vector<CssTrip> &out_trips
) {
    int ell_mult = m - 2;
    assert(tau_k <= ell_mult);
    out_flags = generate_flags(tau_k, tau_code, ell_mult);
    std::unordered_map<u64, int> fidx;
    for (size_t i = 0; i < out_flags.size(); ++i) fidx[out_flags[i]] = (int)i;

    out_denom = factorial(m) / factorial(m - tau_k - 2);
    auto injections = make_injections(m, tau_k);

    int nM = (int)models_m.size();
    std::vector<std::vector<CssTrip>> per_h(nM);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int hi = 0; hi < nM; ++hi) {
        AdjMat H = decode_graph(m, models_m[hi]);
        std::unordered_map<int, std::array<int, 3>> acc; // f -> {chi, sstar, one}
        for (const auto &inj : injections) {
            if (encode_graph(induce(H, inj.data(), tau_k)) != tau_code) continue;
            bool used[8] = {false};
            for (int i = 0; i < tau_k; ++i) used[inj[i]] = true;
            int rem[8], rc = 0;
            for (int i = 0; i < m; ++i) if (!used[i]) rem[rc++] = i;

            // Precompute all_in and no_out for each vertex in rem
            bool all_in[8], no_out[8];
            for (int t = 0; t < rc; ++t) {
                int x = rem[t];
                bool ai = true, no = true;
                for (int i = 0; i < k_orig; ++i) {
                    if (!H.a[inj[i]][x]) ai = false;
                    if (H.a[x][inj[i]]) no = false;
                }
                all_in[t] = ai;
                no_out[t] = no;
            }

            for (int xi = 0; xi < rc; ++xi) {
                for (int yi = 0; yi < rc; ++yi) {
                    if (yi == xi) continue;
                    int x = rem[xi], y = rem[yi];
                    int vf[8], cf = tau_k;
                    for (int i = 0; i < tau_k; ++i) vf[i] = inj[i];
                    for (int j = 0; j < rc; ++j) if (j != xi && j != yi) vf[cf++] = rem[j];
                    int f = fidx.at(canonical_flag_exact(induce(H, vf, ell_mult), tau_k));

                    auto &slot = acc[f];
                    slot[2] += 1; // One
                    if (!all_in[xi] && no_out[xi]) slot[1] += 1; // S*(x)
                    if (all_in[xi] && all_in[yi] && !H.a[x][y] && !H.a[y][x]) slot[0] += 1; // Chi(x, y)
                }
            }
        }
        auto &vec = per_h[hi];
        vec.reserve(acc.size());
        for (auto &kv : acc) {
            vec.push_back({hi, kv.first, kv.second[0], kv.second[1], kv.second[2]});
        }
        std::sort(vec.begin(), vec.end(), [](const CssTrip &x, const CssTrip &y) { return x.f < y.f; });
    }
    out_trips.clear();
    for (int hi = 0; hi < nM; ++hi) out_trips.insert(out_trips.end(), per_h[hi].begin(), per_h[hi].end());
}

// 3. Compute exact SOS-weighted Induction PSD block [[f(sigma) * h_a * h_b]]_tau
//    where h_a, h_b in F^{tau}_{ell} (r = ell - tau_k), requiring tau_k + 1 + 2*r <= m!
//    Choose ordered inj[0..tau_k-1] inducing tau, 1 vertex x in rem,
//    subset R1 of size r from (rem \ {x}), disjoint subset R2 of size r from (rem \ {x} \ R1).
//    Denominator = m! / (r! * r! * (m - tau_k - 1 - 2*r)!).
static void compute_sos_ind_block(
    int m, const std::vector<u64> &models_m,
    int tau_k, u64 tau_code, int k_orig, int ell,
    std::vector<u64> &out_flags,
    std::vector<std::vector<int>> &out_auts,
    long long &out_denom,
    std::vector<PsdTrip> &out_trips
) {
    int r = ell - tau_k;
    int leftover = m - tau_k - 1 - 2 * r;
    assert(leftover >= 0);

    out_flags = generate_flags(tau_k, tau_code, ell);
    out_auts = compute_aut_action_preserving_prefix(tau_k, tau_code, k_orig, ell, out_flags);
    std::unordered_map<u64, int> fidx;
    for (size_t i = 0; i < out_flags.size(); ++i) fidx[out_flags[i]] = (int)i;

    out_denom = factorial(m) / (factorial(r) * factorial(r) * factorial(leftover));
    auto injections = make_injections(m, tau_k);

    int rem2_n = m - tau_k - 1;
    std::vector<std::pair<int, int>> mask_pairs;
    for (int m1 = 0; m1 < (1 << rem2_n); ++m1) {
        if (__builtin_popcount(m1) != r) continue;
        for (int m2 = 0; m2 < (1 << rem2_n); ++m2) {
            if ((m1 & m2) != 0) continue;
            if (__builtin_popcount(m2) != r) continue;
            mask_pairs.push_back({m1, m2});
        }
    }

    int nM = (int)models_m.size();
    std::vector<std::vector<PsdTrip>> per_h(nM);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int hi = 0; hi < nM; ++hi) {
        AdjMat H = decode_graph(m, models_m[hi]);
        std::unordered_map<uint32_t, std::array<int, 3>> acc;
        for (const auto &inj : injections) {
            if (encode_graph(induce(H, inj.data(), tau_k)) != tau_code) continue;
            bool used[8] = {false};
            for (int i = 0; i < tau_k; ++i) used[inj[i]] = true;
            int rem[8], rc = 0;
            for (int i = 0; i < m; ++i) if (!used[i]) rem[rc++] = i;

            for (int xi = 0; xi < rc; ++xi) {
                int x = rem[xi];
                bool all_in = true, no_out = true;
                for (int i = 0; i < k_orig; ++i) {
                    if (!H.a[inj[i]][x]) all_in = false;
                    if (H.a[x][inj[i]]) no_out = false;
                }
                int w_sstar = (!all_in && no_out) ? 1 : 0;
                int w_f0 = all_in ? 1 : 0;

                int rem2[8], r2c = 0;
                for (int j = 0; j < rc; ++j) if (j != xi) rem2[r2c++] = rem[j];

                int v1[8], v2[8];
                for (int i = 0; i < tau_k; ++i) v1[i] = v2[i] = inj[i];

                for (auto [m1, m2] : mask_pairs) {
                    int c1 = tau_k, c2 = tau_k;
                    for (int j = 0; j < r2c; ++j) {
                        if ((m1 >> j) & 1) v1[c1++] = rem2[j];
                        else if ((m2 >> j) & 1) v2[c2++] = rem2[j];
                    }
                    int a = fidx.at(canonical_flag_exact(induce(H, v1, ell), tau_k));
                    int b = fidx.at(canonical_flag_exact(induce(H, v2, ell), tau_k));
                    uint32_t key = ((uint32_t)a << 16) | (uint32_t)b;
                    auto &slot = acc[key];
                    slot[0] += w_sstar;
                    slot[1] += w_f0;
                    slot[2] += 1;
                }
            }
        }
        auto &vec = per_h[hi];
        vec.reserve(acc.size());
        for (auto &kv : acc) {
            int a = (int)(kv.first >> 16), b = (int)(kv.first & 0xFFFFU);
            vec.push_back({hi, a, b, kv.second[0], kv.second[1], kv.second[2]});
        }
        std::sort(vec.begin(), vec.end(), [](const PsdTrip &x, const PsdTrip &y) {
            return (x.a != y.a) ? (x.a < y.a) : (x.b < y.b);
        });
    }
    out_trips.clear();
    for (int hi = 0; hi < nM; ++hi) out_trips.insert(out_trips.end(), per_h[hi].begin(), per_h[hi].end());
}

// 4. Compute exact SOS-weighted CSS PSD block [[g_CSS(sigma, r) * h_a * h_b]]_tau
//    requiring tau_k + 2 + 2*r <= m!
//    Denominator = m! / (r! * r! * (m - tau_k - 2 - 2*r)!).
static void compute_sos_css_block(
    int m, const std::vector<u64> &models_m,
    int tau_k, u64 tau_code, int k_orig, int ell,
    std::vector<u64> &out_flags,
    std::vector<std::vector<int>> &out_auts,
    long long &out_denom,
    std::vector<PsdTrip> &out_trips
) {
    int r = ell - tau_k;
    int leftover = m - tau_k - 2 - 2 * r;
    assert(leftover >= 0);

    out_flags = generate_flags(tau_k, tau_code, ell);
    out_auts = compute_aut_action_preserving_prefix(tau_k, tau_code, k_orig, ell, out_flags);
    std::unordered_map<u64, int> fidx;
    for (size_t i = 0; i < out_flags.size(); ++i) fidx[out_flags[i]] = (int)i;

    out_denom = factorial(m) / (factorial(r) * factorial(r) * factorial(leftover));
    auto injections = make_injections(m, tau_k);

    int rem2_n = m - tau_k - 2;
    std::vector<std::pair<int, int>> mask_pairs;
    for (int m1 = 0; m1 < (1 << rem2_n); ++m1) {
        if (__builtin_popcount(m1) != r) continue;
        for (int m2 = 0; m2 < (1 << rem2_n); ++m2) {
            if ((m1 & m2) != 0) continue;
            if (__builtin_popcount(m2) != r) continue;
            mask_pairs.push_back({m1, m2});
        }
    }

    int nM = (int)models_m.size();
    std::vector<std::vector<PsdTrip>> per_h(nM);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int hi = 0; hi < nM; ++hi) {
        AdjMat H = decode_graph(m, models_m[hi]);
        std::unordered_map<uint32_t, std::array<int, 3>> acc;
        for (const auto &inj : injections) {
            if (encode_graph(induce(H, inj.data(), tau_k)) != tau_code) continue;
            bool used[8] = {false};
            for (int i = 0; i < tau_k; ++i) used[inj[i]] = true;
            int rem[8], rc = 0;
            for (int i = 0; i < m; ++i) if (!used[i]) rem[rc++] = i;

            bool all_in[8], no_out[8];
            for (int t = 0; t < rc; ++t) {
                int x = rem[t];
                bool ai = true, no = true;
                for (int i = 0; i < k_orig; ++i) {
                    if (!H.a[inj[i]][x]) ai = false;
                    if (H.a[x][inj[i]]) no = false;
                }
                all_in[t] = ai;
                no_out[t] = no;
            }

            for (int xi = 0; xi < rc; ++xi) {
                for (int yi = 0; yi < rc; ++yi) {
                    if (yi == xi) continue;
                    int x = rem[xi], y = rem[yi];
                    int w_chi = (all_in[xi] && all_in[yi] && !H.a[x][y] && !H.a[y][x]) ? 1 : 0;
                    int w_sstar = (!all_in[xi] && no_out[xi]) ? 1 : 0;

                    int rem2[8], r2c = 0;
                    for (int j = 0; j < rc; ++j) if (j != xi && j != yi) rem2[r2c++] = rem[j];
                    int v1[8], v2[8];
                    for (int i = 0; i < tau_k; ++i) v1[i] = v2[i] = inj[i];

                    for (auto [m1, m2] : mask_pairs) {
                        int c1 = tau_k, c2 = tau_k;
                        for (int j = 0; j < r2c; ++j) {
                            if ((m1 >> j) & 1) v1[c1++] = rem2[j];
                            else if ((m2 >> j) & 1) v2[c2++] = rem2[j];
                        }
                        int a = fidx.at(canonical_flag_exact(induce(H, v1, ell), tau_k));
                        int b = fidx.at(canonical_flag_exact(induce(H, v2, ell), tau_k));
                        uint32_t key = ((uint32_t)a << 16) | (uint32_t)b;
                        auto &slot = acc[key];
                        slot[0] += w_chi;
                        slot[1] += w_sstar;
                        slot[2] += 1;
                    }
                }
            }
        }
        auto &vec = per_h[hi];
        vec.reserve(acc.size());
        for (auto &kv : acc) {
            int a = (int)(kv.first >> 16), b = (int)(kv.first & 0xFFFFU);
            vec.push_back({hi, a, b, kv.second[0], kv.second[1], kv.second[2]});
        }
        std::sort(vec.begin(), vec.end(), [](const PsdTrip &x, const PsdTrip &y) {
            return (x.a != y.a) ? (x.a < y.a) : (x.b < y.b);
        });
    }
    out_trips.clear();
    for (int hi = 0; hi < nM; ++hi) out_trips.insert(out_trips.end(), per_h[hi].begin(), per_h[hi].end());
}

int main(int argc, char **argv) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <flags_m.bin> <out_ext.bin>\n";
        return 1;
    }
    // Load exact model list from flags_m<m>.bin
    std::ifstream in(argv[1], std::ios::binary);
    assert(in.good());
    int32_t magic, m, nM;
    in.read((char *)&magic, 4);
    in.read((char *)&m, 4);
    in.read((char *)&nM, 4);
    assert(magic == 0x464C4147);
    std::vector<u64> models_m(nM);
    in.read((char *)models_m.data(), 8LL * nM);
    in.close();

    auto small_models = generate_models(m - 1);

    std::ofstream out(argv[2], std::ios::binary);
    assert(out.good());
    w_i32(out, 0x45585446); // "EXTF"
    w_i32(out, m);
    w_i32(out, nM);

    // === 1. Build ALL Linear Induction Families ===
    struct Spec { int tau_k; u64 tau_code; int k_orig; int is_lifted; };
    std::vector<Spec> ind_specs;
    for (int k = 1; k <= m - 1; ++k) {
        for (u64 sc : small_models[k]) {
            if (has_sink_root(k, sc)) {
                ind_specs.push_back({k, sc, k, 0});
            } else if (k <= m - 2) {
                ind_specs.push_back({k + 1, lift_f0_type(k, sc), k, 1});
            }
        }
    }
    std::cerr << "Generating " << ind_specs.size() << " linear Induction families for m=" << m << "...\n";
    w_i32(out, (int32_t)ind_specs.size());
    long long total_ind_rows = 0;
    for (const auto &sp : ind_specs) {
        std::vector<u64> fl;
        long long denom = 0;
        std::vector<LinTrip> trips;
        compute_linear_ind_family(m, models_m, sp.tau_k, sp.tau_code, sp.k_orig, fl, denom, trips);
        total_ind_rows += fl.size();
        w_i32(out, sp.tau_k);
        w_u64(out, sp.tau_code);
        w_i32(out, sp.k_orig);
        w_i32(out, sp.is_lifted);
        w_i32(out, (int32_t)fl.size());
        for (u64 fc : fl) w_u64(out, fc);
        w_i64(out, denom);
        w_i64(out, (int64_t)trips.size());
        out.write((const char *)trips.data(), trips.size() * sizeof(LinTrip));
    }
    std::cerr << "  total linear Induction rows = " << total_ind_rows << "\n";

    // === 2. Build ALL Linear CSS Families ===
    std::vector<Spec> css_specs;
    for (int k = 1; k <= m - 2; ++k) {
        for (u64 sc : small_models[k]) {
            if (has_sink_root(k, sc)) {
                css_specs.push_back({k, sc, k, 0});
            } else if (k <= m - 3) {
                css_specs.push_back({k + 1, lift_f0_type(k, sc), k, 1});
            }
        }
    }
    std::cerr << "Generating " << css_specs.size() << " linear CSS families for m=" << m << "...\n";
    w_i32(out, (int32_t)css_specs.size());
    long long total_css_base_rows = 0;
    for (const auto &sp : css_specs) {
        std::vector<u64> fl;
        long long denom = 0;
        std::vector<CssTrip> trips;
        compute_linear_css_family(m, models_m, sp.tau_k, sp.tau_code, sp.k_orig, fl, denom, trips);
        total_css_base_rows += fl.size();
        w_i32(out, sp.tau_k);
        w_u64(out, sp.tau_code);
        w_i32(out, sp.k_orig);
        w_i32(out, sp.is_lifted);
        w_i32(out, (int32_t)fl.size());
        for (u64 fc : fl) w_u64(out, fc);
        w_i64(out, denom);
        w_i64(out, (int64_t)trips.size());
        out.write((const char *)trips.data(), trips.size() * sizeof(CssTrip));
    }
    std::cerr << "  total linear CSS base rows (x |R| tangents) = " << total_css_base_rows << "\n";

    // === 3. Build SOS-Weighted Induction PSD Blocks ===
    struct SosSpec { int tau_k; u64 tau_code; int k_orig; int is_lifted; int ell; };
    std::vector<SosSpec> sos_ind_specs;
    for (int k = 1; k <= m - 3; ++k) {
        for (u64 sc : small_models[k]) {
            if (has_sink_root(k, sc)) {
                int ell = (m + k - 1) / 2;
                if (ell > k && k + 1 + 2 * (ell - k) <= m) {
                    // Only tight parity (or k=1 at m=5 lifts 4->5 too!)
                    if (k + 1 + 2 * (ell - k) == m || (m == 5 && k == 1 && ell == 2))
                        sos_ind_specs.push_back({k, sc, k, 0, ell});
                }
            } else {
                int tau_k = k + 1;
                int ell = (m + tau_k - 1) / 2;
                if (ell > tau_k && tau_k + 1 + 2 * (ell - tau_k) == m) {
                    sos_ind_specs.push_back({tau_k, lift_f0_type(k, sc), k, 1, ell});
                }
            }
        }
        // Also for m=6, k=2 (beta) lifted to T (tau_k=3, ell=4): pi^{T, {0,1}}(f(beta))!
        if (m == 6 && k == 2) {
            for (u64 sc : small_models[2]) {
                if (has_sink_root(2, sc)) {
                    // beta -> T = F0(beta)
                    sos_ind_specs.push_back({3, lift_f0_type(2, sc), 2, 1, 4});
                }
            }
        }
    }
    std::cerr << "Generating " << sos_ind_specs.size() << " SOS-weighted Induction PSD blocks for m=" << m << "...\n";
    w_i32(out, (int32_t)sos_ind_specs.size());
    for (const auto &sp : sos_ind_specs) {
        std::vector<u64> fl;
        std::vector<std::vector<int>> auts;
        long long denom = 0;
        std::vector<PsdTrip> trips;
        compute_sos_ind_block(m, models_m, sp.tau_k, sp.tau_code, sp.k_orig, sp.ell, fl, auts, denom, trips);
        std::cerr << "  SOS-Ind tau_k=" << sp.tau_k << " code=" << sp.tau_code
                  << " k_orig=" << sp.k_orig << " ell=" << sp.ell
                  << " |flags|=" << fl.size() << " |Aut|=" << auts.size() << " nnz=" << trips.size() << "\n";
        w_i32(out, sp.tau_k);
        w_u64(out, sp.tau_code);
        w_i32(out, sp.k_orig);
        w_i32(out, sp.is_lifted);
        w_i32(out, sp.ell);
        w_i32(out, (int32_t)fl.size());
        for (u64 fc : fl) w_u64(out, fc);
        w_i32(out, (int32_t)auts.size());
        for (const auto &a : auts)
            for (int x : a) w_i32(out, x);
        w_i64(out, denom);
        w_i64(out, (int64_t)trips.size());
        out.write((const char *)trips.data(), trips.size() * sizeof(PsdTrip));
    }

    // === 4. Build SOS-Weighted CSS PSD Blocks ===
    std::vector<SosSpec> sos_css_specs;
    for (int k = 1; k <= m - 4; ++k) {
        for (u64 sc : small_models[k]) {
            if (has_sink_root(k, sc)) {
                int ell = (m + k - 2) / 2;
                if (ell > k && k + 2 + 2 * (ell - k) == m) {
                    sos_css_specs.push_back({k, sc, k, 0, ell});
                }
            }
        }
    }
    std::cerr << "Generating " << sos_css_specs.size() << " SOS-weighted CSS PSD blocks for m=" << m << "...\n";
    w_i32(out, (int32_t)sos_css_specs.size());
    for (const auto &sp : sos_css_specs) {
        std::vector<u64> fl;
        std::vector<std::vector<int>> auts;
        long long denom = 0;
        std::vector<PsdTrip> trips;
        compute_sos_css_block(m, models_m, sp.tau_k, sp.tau_code, sp.k_orig, sp.ell, fl, auts, denom, trips);
        std::cerr << "  SOS-CSS tau_k=" << sp.tau_k << " code=" << sp.tau_code
                  << " ell=" << sp.ell << " |flags|=" << fl.size()
                  << " |Aut|=" << auts.size() << " nnz=" << trips.size() << "\n";
        w_i32(out, sp.tau_k);
        w_u64(out, sp.tau_code);
        w_i32(out, sp.k_orig);
        w_i32(out, sp.is_lifted);
        w_i32(out, sp.ell);
        w_i32(out, (int32_t)fl.size());
        for (u64 fc : fl) w_u64(out, fc);
        w_i32(out, (int32_t)auts.size());
        for (const auto &a : auts)
            for (int x : a) w_i32(out, x);
        w_i64(out, denom);
        w_i64(out, (int64_t)trips.size());
        out.write((const char *)trips.data(), trips.size() * sizeof(PsdTrip));
    }

    out.close();
    std::cerr << "Wrote " << argv[2] << "\n";
    return 0;
}
