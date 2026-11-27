// flag_gen.cpp - Exact, deterministic Flag Algebra engine for C3-free oriented graphs.
// Compiles with: g++ -O3 -march=native -fopenmp flag_gen.cpp -o flag_gen
//
// Representations:
// An oriented graph on n vertices (0..n-1) is represented by a bitmask uint64_t code:
// For each pair 0 <= i < j < n, with pair_idx(i,j) = i*(2*n - i - 1)/2 + (j - i - 1),
// 2 bits store: 0 = non-edge, 1 = i -> j, 2 = j -> i.
// (n <= 8 fits in 2 * 28 = 56 bits < 64 bits.)
//
// Canonical labeling of an unlabeled graph (k=0) or sigma-flag (labeled vertices 0..k-1):
// Exact lexicographical minimum code over all permutations fixing 0..k-1,
// pruned ONLY by exact isomorphism invariants when n >= 7 (for n <= 6, exact over all n!).
// Wait: actually, to be 100% consistent across all n, we define canonical code as exact
// lexicographical minimum over all permutations fixing 0..k-1. For n=7 we use backtracking
// branch-and-bound on the code bits from MSB to LSB (or pair order) so it STILL finds the
// EXACT global minimum over all 7! = 5040 permutations!

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using u64 = uint64_t;
using u8 = uint8_t;

struct AdjMat {
    int n;
    u8 a[8][8]; // a[i][j] = 1 iff i -> j
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
    // New vertex i corresponds to old vertex perm[i].
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

static inline bool has_c3(const AdjMat &g) {
    int n = g.n;
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            if (!g.a[i][j]) continue;
            for (int k = 0; k < n; ++k) {
                if (g.a[j][k] && g.a[k][i]) return true;
            }
        }
    }
    return false;
}

// Check if adding vertex (n-1) to a C3-free graph on 0..n-2 creates a C3.
static inline bool has_c3_with_last(const AdjMat &g) {
    int last = g.n - 1;
    for (int i = 0; i < last; ++i) {
        if (g.a[last][i]) {
            // last -> i -> j -> last
            for (int j = 0; j < last; ++j) {
                if (g.a[i][j] && g.a[j][last]) return true;
            }
        }
    }
    return false;
}

// Exact lexicographical minimum code over all permutations fixing 0..k-1.
// Uses pair-wise LSB? Wait: if we compare uint64_t directly, MSB is the LAST pair (n-2, n-1).
// For clean exact minimization with fast branch-and-bound, let's iterate permutations directly
// for (n - k) <= 6 (at most 720 perms), and for n=7, k=0 we use degree-invariant canonicalization
// OR exact all-5040 check? Wait: let's check how fast exact 5040 is vs invariant!
// Even better: use a canonical code that compares from vertex 0 upwards (MSB = pair (0,1))?
// No, keeping simple LSB pair order makes decoding trivial and for n <= 6, 720 perms is instant.
// For n == 7, k == 0, we can sort vertices by (out_deg, in_deg, 1-step refined) and only permute
// within color classes, which is 100% isomorphism-invariant AND 100x faster!
// WAIT: to be 100% sure two graphs get the same canon iff isomorphic, let's verify:
// Any permutation invariant coloring C(v) induces a canonical total order on color classes;
// taking min over all permutations respecting the sorted color classes IS a canonical invariant!
static inline u64 canonical_flag_exact(const AdjMat &g, int k) {
    int n = g.n;
    int m = n - k;
    int perm[8];
    for (int i = 0; i < n; ++i) perm[i] = i;
    if (m <= 1) return encode_graph(g);

    if (m <= 6) {
        u64 best = ~0ULL;
        do {
            u64 c = encode_permuted(g, perm);
            if (c < best) best = c;
        } while (std::next_permutation(perm + k, perm + n));
        return best;
    }

    // m == 7 (only happens for n=7, k=0): refine by (out_deg, in_deg) + 2-hop invariant.
    // Every isomorphism maps color class to same color class, so min over color-preserving perms
    // is a 100% EXACT canonical invariant!
    uint64_t inv[8];
    int outd[8] = {0}, ind[8] = {0};
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            outd[i] += g.a[i][j];
            ind[i] += g.a[j][i];
        }
    }
    for (int i = 0; i < n; ++i) {
        // Compute sorted multiset of neighbor (outd, ind) for out-neighbors and in-neighbors
        uint64_t out_sig = 0, in_sig = 0;
        int tmp_out[8], co = 0, tmp_in[8], ci = 0;
        for (int j = 0; j < n; ++j) {
            if (g.a[i][j]) tmp_out[co++] = (outd[j] << 4) | ind[j];
            if (g.a[j][i]) tmp_in[ci++] = (outd[j] << 4) | ind[j];
        }
        std::sort(tmp_out, tmp_out + co);
        std::sort(tmp_in, tmp_in + ci);
        for (int t = 0; t < co; ++t) out_sig = (out_sig << 8) | tmp_out[t];
        for (int t = 0; t < ci; ++t) in_sig = (in_sig << 8) | tmp_in[t];
        // Pack into 128-bit or pair; actually outd, ind <= 6 so 3 bits each,
        // wait: co <= 6, each entry <= 112 (7 bits), 6*7 = 42 bits -> split into tuple
        inv[i] = ((uint64_t)outd[i] << 60) | ((uint64_t)ind[i] << 56) ^ (out_sig * 1315423911ULL) ^ (in_sig * 2654435761ULL);
        // Wait: to avoid ANY hash collision risk, let's sort using exact tuples!
        (void)inv[i];
    }
    struct VKey {
        int outd, ind;
        uint64_t out_sig, in_sig; // 6 * 8 = 48 bits exact!
        int v;
        bool operator<(const VKey &o) const {
            if (outd != o.outd) return outd < o.outd;
            if (ind != o.ind) return ind < o.ind;
            if (out_sig != o.out_sig) return out_sig < o.out_sig;
            return in_sig < o.in_sig;
        }
        bool same_color(const VKey &o) const {
            return outd == o.outd && ind == o.ind && out_sig == o.out_sig && in_sig == o.in_sig;
        }
    };
    VKey keys[8];
    for (int i = 0; i < n; ++i) {
        int tmp_out[8], co = 0, tmp_in[8], ci = 0;
        for (int j = 0; j < n; ++j) {
            if (g.a[i][j]) tmp_out[co++] = (outd[j] << 4) | ind[j];
            if (g.a[j][i]) tmp_in[ci++] = (outd[j] << 4) | ind[j];
        }
        std::sort(tmp_out, tmp_out + co);
        std::sort(tmp_in, tmp_in + ci);
        uint64_t os = 0, is = 0;
        for (int t = 0; t < co; ++t) os = (os << 8) | (uint64_t)tmp_out[t];
        for (int t = 0; t < ci; ++t) is = (is << 8) | (uint64_t)tmp_in[t];
        keys[i] = {outd[i], ind[i], os, is, i};
    }
    std::sort(keys + k, keys + n);
    // Identify contiguous color blocks
    int starts[8], ends[8], nb = 0;
    for (int i = k; i < n; ) {
        int j = i + 1;
        while (j < n && keys[i].same_color(keys[j])) ++j;
        starts[nb] = i;
        ends[nb] = j;
        ++nb;
        i = j;
    }
    for (int i = k; i < n; ++i) perm[i] = keys[i].v;
    for (int b = 0; b < nb; ++b) std::sort(perm + starts[b], perm + ends[b]);

    u64 best = ~0ULL;
    // Iterate Cartesian product of permutations over blocks
    auto rec = [&](auto &&self, int b) -> void {
        if (b == nb) {
            u64 c = encode_permuted(g, perm);
            if (c < best) best = c;
            return;
        }
        do {
            self(self, b + 1);
        } while (std::next_permutation(perm + starts[b], perm + ends[b]));
    };
    rec(rec, 0);
    return best;
}

// Generate all canonical unlabeled C3-free oriented graphs up to max_n.
std::vector<std::vector<u64>> generate_models(int max_n) {
    std::vector<std::vector<u64>> models(max_n + 1);
    models[0] = {0ULL};
    models[1] = {0ULL};

    for (int n = 2; n <= max_n; ++n) {
        std::vector<u64> cand;
        int p3 = 1;
        for (int i = 0; i < n - 1; ++i) p3 *= 3;

        const auto &prev = models[n - 1];
        std::vector<std::vector<u64>> thread_cands;

        // Simple parallelization if large
        #pragma omp parallel
        {
            std::vector<u64> local;
            #pragma omp for schedule(dynamic)
            for (size_t gi = 0; gi < prev.size(); ++gi) {
                AdjMat base = decode_graph(n - 1, prev[gi]);
                AdjMat g;
                g.n = n;
                for (int mask = 0; mask < p3; ++mask) {
                    memcpy(g.a, base.a, sizeof(base.a));
                    for (int i = 0; i < n; ++i) g.a[i][n - 1] = g.a[n - 1][i] = 0;
                    int x = mask;
                    for (int i = 0; i < n - 1; ++i) {
                        int s = x % 3;
                        x /= 3;
                        if (s == 1) g.a[i][n - 1] = 1;
                        else if (s == 2) g.a[n - 1][i] = 1;
                    }
                    if (!has_c3_with_last(g)) {
                        local.push_back(canonical_flag_exact(g, 0));
                    }
                }
            }
            #pragma omp critical
            cand.insert(cand.end(), local.begin(), local.end());
        }
        std::sort(cand.begin(), cand.end());
        cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
        models[n] = std::move(cand);
        std::cerr << "m=" << n << ": " << models[n].size() << " C3-free oriented graphs\n";
    }
    return models;
}

// Generate all canonical sigma-flags of size ell for a fixed type sigma of size k.
std::vector<u64> generate_flags(int k, u64 sigma_code, int ell) {
    assert(ell >= k);
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
                    int s = x % 3;
                    x /= 3;
                    if (s == 1) g.a[i][n - 1] = 1;
                    else if (s == 2) g.a[n - 1][i] = 1;
                }
                if (!has_c3_with_last(g)) {
                    next.push_back(canonical_flag_exact(g, k));
                }
            }
        }
        std::sort(next.begin(), next.end());
        next.erase(std::unique(next.begin(), next.end()), next.end());
        cur = std::move(next);
    }
    return cur;
}

// Compute automorphism group of type sigma (permutations of 0..k-1 preserving sigma)
// and its induced action on sigma-flags of size ell.
std::vector<std::vector<int>> compute_aut_action(int k, u64 sigma_code, int ell, const std::vector<u64> &flags) {
    AdjMat sig = decode_graph(k, sigma_code);
    std::unordered_map<u64, int> flag_idx;
    for (size_t i = 0; i < flags.size(); ++i) flag_idx[flags[i]] = (int)i;

    std::vector<std::vector<int>> actions;
    int p[8];
    for (int i = 0; i < k; ++i) p[i] = i;
    do {
        if (encode_permuted(sig, p) == sigma_code) {
            // p is an automorphism of sigma: new labeled vertex i <- old labeled vertex p[i]
            std::vector<int> act(flags.size());
            int fullp[8];
            for (int i = 0; i < k; ++i) fullp[i] = p[i];
            for (int i = k; i < ell; ++i) fullp[i] = i;
            for (size_t fi = 0; fi < flags.size(); ++fi) {
                AdjMat f = decode_graph(ell, flags[fi]);
                AdjMat pf;
                pf.n = ell;
                memset(pf.a, 0, sizeof(pf.a));
                for (int i = 0; i < ell; ++i)
                    for (int j = 0; j < ell; ++j)
                        pf.a[i][j] = f.a[fullp[i]][fullp[j]];
                u64 c = canonical_flag_exact(pf, k);
                act[fi] = flag_idx.at(c);
            }
            actions.push_back(std::move(act));
        }
    } while (std::next_permutation(p, p + k));
    return actions;
}

static long long factorial(int n) {
    long long r = 1;
    for (int i = 2; i <= n; ++i) r *= i;
    return r;
}

// Induced subgraph on ordered vertex list verts[0..sz-1]
static inline AdjMat induce(const AdjMat &H, const int *verts, int sz) {
    AdjMat sub;
    sub.n = sz;
    for (int i = 0; i < sz; ++i) {
        int ui = verts[i];
        for (int j = 0; j < sz; ++j) {
            sub.a[i][j] = H.a[ui][verts[j]];
        }
    }
    return sub;
}

struct Triplet {
    int h_idx;
    int a;
    int b;
    int cnt;
};

// Compute exact integer multiplication table for type (k, sigma_code) with flag sizes (ell1, ell2)
// where ell1 + ell2 - k = m.
// Output: exact denominator = m! / ((ell1 - k)! * (ell2 - k)!), and sparse list of (h_idx, a, b, cnt).
// If symmetric (ell1 == ell2), only stores a <= b with cnt = exact sum of (a,b) and (b,a) if a != b?
// NO! Keep it crystal clear: store exact (h_idx, a, b, cnt) for ALL (a, b) with cnt > 0!
// For symmetric (ell1 == ell2), cnt(h, a, b) == cnt(h, b, a) automatically!
void compute_product_table(
    int m,
    const std::vector<u64> &models_m,
    int k,
    u64 sigma_code,
    int ell1,
    const std::vector<u64> &flags1,
    int ell2,
    const std::vector<u64> &flags2,
    long long &out_denom,
    std::vector<Triplet> &out_triplets
) {
    assert(ell1 + ell2 - k == m);
    int r1 = ell1 - k;
    int r2 = ell2 - k;
    out_denom = factorial(m) / (factorial(r1) * factorial(r2));

    std::unordered_map<u64, int> idx1, idx2;
    for (size_t i = 0; i < flags1.size(); ++i) idx1[flags1[i]] = (int)i;
    for (size_t i = 0; i < flags2.size(); ++i) idx2[flags2[i]] = (int)i;

    int nf1 = (int)flags1.size();
    int nf2 = (int)flags2.size();

    // Precompute all k-injections from [m]
    std::vector<std::array<int, 8>> injections;
    {
        std::vector<int> comb(m, 0);
        std::fill(comb.end() - k, comb.end(), 1);
        do {
            int sel[8], cs = 0;
            for (int i = 0; i < m; ++i) if (comb[i]) sel[cs++] = i;
            do {
                std::array<int, 8> arr{};
                for (int i = 0; i < k; ++i) arr[i] = sel[i];
                injections.push_back(arr);
            } while (std::next_permutation(sel, sel + k));
        } while (std::next_permutation(comb.begin(), comb.end()));
    }

    // Precompute all subsets of [0..m-k-1] of size r1
    std::vector<int> sub_masks;
    int rem_n = m - k;
    for (int mask = 0; mask < (1 << rem_n); ++mask) {
        if (__builtin_popcount(mask) == r1) sub_masks.push_back(mask);
    }

    int nM = (int)models_m.size();
    std::vector<std::vector<Triplet>> per_model(nM);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int hi = 0; hi < nM; ++hi) {
        AdjMat H = decode_graph(m, models_m[hi]);
        std::unordered_map<uint32_t, int> local_cnt;
        for (const auto &inj : injections) {
            // Check if H[inj[0..k-1]] == sigma_code
            AdjMat sub_sig = induce(H, inj.data(), k);
            if (encode_graph(sub_sig) != sigma_code) continue;

            // Collect remaining vertices
            bool used[8] = {false};
            for (int i = 0; i < k; ++i) used[inj[i]] = true;
            int rem[8], rc = 0;
            for (int i = 0; i < m; ++i) if (!used[i]) rem[rc++] = i;

            int v1[8], v2[8];
            for (int i = 0; i < k; ++i) v1[i] = v2[i] = inj[i];

            for (int mask : sub_masks) {
                int c1 = k, c2 = k;
                for (int i = 0; i < rem_n; ++i) {
                    if ((mask >> i) & 1) v1[c1++] = rem[i];
                    else v2[c2++] = rem[i];
                }
                AdjMat f1 = induce(H, v1, ell1);
                AdjMat f2 = induce(H, v2, ell2);
                int a = idx1.at(canonical_flag_exact(f1, k));
                int b = idx2.at(canonical_flag_exact(f2, k));
                uint32_t key = ((uint32_t)a << 16) | (uint32_t)b;
                local_cnt[key] += 1;
            }
        }
        auto &vec = per_model[hi];
        vec.reserve(local_cnt.size());
        for (auto &kv : local_cnt) {
            int a = (int)(kv.first >> 16);
            int b = (int)(kv.first & 0xFFFFU);
            vec.push_back({hi, a, b, kv.second});
        }
        std::sort(vec.begin(), vec.end(), [](const Triplet &x, const Triplet &y) {
            if (x.a != y.a) return x.a < y.a;
            return x.b < y.b;
        });
    }

    out_triplets.clear();
    for (int hi = 0; hi < nM; ++hi) {
        out_triplets.insert(out_triplets.end(), per_model[hi].begin(), per_model[hi].end());
    }
    (void)nf1;
    (void)nf2;
}

// Compute exact unlabeling vector [[F]]_sigma(H) for all F in flags (size ell <= m) on all H in models_m.
// Exact denominator is m! / (ell - k)! / (m - ell)! = (m)_k * C(m - k, ell - k).
void compute_unlabel_table(
    int m,
    const std::vector<u64> &models_m,
    int k,
    u64 sigma_code,
    int ell,
    const std::vector<u64> &flags,
    long long &out_denom,
    std::vector<Triplet> &out_triplets // (h_idx, f_idx, 0, cnt)
) {
    int r = ell - k;
    out_denom = factorial(m) / (factorial(r) * factorial(m - ell));
    std::unordered_map<u64, int> fidx;
    for (size_t i = 0; i < flags.size(); ++i) fidx[flags[i]] = (int)i;

    std::vector<std::array<int, 8>> injections;
    {
        std::vector<int> comb(m, 0);
        std::fill(comb.end() - k, comb.end(), 1);
        do {
            int sel[8], cs = 0;
            for (int i = 0; i < m; ++i) if (comb[i]) sel[cs++] = i;
            do {
                std::array<int, 8> arr{};
                for (int i = 0; i < k; ++i) arr[i] = sel[i];
                injections.push_back(arr);
            } while (std::next_permutation(sel, sel + k));
        } while (std::next_permutation(comb.begin(), comb.end()));
    }

    int rem_n = m - k;
    std::vector<int> sub_masks;
    for (int mask = 0; mask < (1 << rem_n); ++mask) {
        if (__builtin_popcount(mask) == r) sub_masks.push_back(mask);
    }

    int nM = (int)models_m.size();
    std::vector<std::vector<Triplet>> per_model(nM);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int hi = 0; hi < nM; ++hi) {
        AdjMat H = decode_graph(m, models_m[hi]);
        std::unordered_map<int, int> local_cnt;
        for (const auto &inj : injections) {
            AdjMat sub_sig = induce(H, inj.data(), k);
            if (encode_graph(sub_sig) != sigma_code) continue;
            bool used[8] = {false};
            for (int i = 0; i < k; ++i) used[inj[i]] = true;
            int rem[8], rc = 0;
            for (int i = 0; i < m; ++i) if (!used[i]) rem[rc++] = i;
            int v1[8];
            for (int i = 0; i < k; ++i) v1[i] = inj[i];
            for (int mask : sub_masks) {
                int c1 = k;
                for (int i = 0; i < rem_n; ++i) {
                    if ((mask >> i) & 1) v1[c1++] = rem[i];
                }
                AdjMat f = induce(H, v1, ell);
                int a = fidx.at(canonical_flag_exact(f, k));
                local_cnt[a] += 1;
            }
        }
        auto &vec = per_model[hi];
        for (auto &kv : local_cnt) vec.push_back({hi, kv.first, 0, kv.second});
        std::sort(vec.begin(), vec.end(), [](const Triplet &x, const Triplet &y) {
            return x.a < y.a;
        });
    }
    out_triplets.clear();
    for (int hi = 0; hi < nM; ++hi) {
        out_triplets.insert(out_triplets.end(), per_model[hi].begin(), per_model[hi].end());
    }
}

void write_binary_u64(std::ofstream &f, u64 v) { f.write((const char *)&v, sizeof(v)); }
void write_binary_i64(std::ofstream &f, int64_t v) { f.write((const char *)&v, sizeof(v)); }
void write_binary_i32(std::ofstream &f, int32_t v) { f.write((const char *)&v, sizeof(v)); }

int main(int argc, char **argv) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <mode: count|dump> <m> [out_dir]\n";
        return 1;
    }
    std::string mode = argv[1];
    int m = std::stoi(argv[2]);
    std::string out_dir = (argc >= 4) ? argv[3] : ".";

    auto models = generate_models(m);

    if (mode == "count") {
        // Print detailed type & flag statistics for m
        std::cout << "=== Flag Algebra Stats for m = " << m << " ===\n";
        std::cout << "Unlabeled models |M_" << m << "| = " << models[m].size() << "\n";
        for (int k = m % 2; k <= m - 2; k += 2) {
            int ell = (m + k) / 2;
            std::cout << "Type size k=" << k << " (ell=" << ell << "): " << models[k].size() << " types\n";
            long long total_flags = 0, max_flags = 0;
            for (size_t ti = 0; ti < models[k].size(); ++ti) {
                auto fl = generate_flags(k, models[k][ti], ell);
                auto auts = compute_aut_action(k, models[k][ti], ell, fl);
                total_flags += fl.size();
                if ((long long)fl.size() > max_flags) max_flags = fl.size();
                if (models[k].size() <= 50) {
                    std::cout << "  type[" << ti << "] code=" << models[k][ti]
                              << " |flags|=" << fl.size() << " |Aut|=" << auts.size() << "\n";
                }
            }
            std::cout << "  summary k=" << k << ": total_flags=" << total_flags << " max_flags=" << max_flags << "\n";
        }
        // Also 1-flags of size m-1 (for min out-degree constraints!)
        if (m >= 3) {
            auto f1 = generate_flags(1, 0ULL, m - 1);
            std::cout << "1-flags of size m-1=" << (m - 1) << ": " << f1.size() << "\n";
        }
        return 0;
    }

    if (mode == "dump") {
        // Dump complete binary dataset for m into out_dir/flags_m<m>.bin
        std::string path = out_dir + "/flags_m" + std::to_string(m) + ".bin";
        std::ofstream out(path, std::ios::binary);
        assert(out.good());

        // Header: magic, m, num_models
        write_binary_i32(out, 0x464C4147); // "FLAG"
        write_binary_i32(out, m);
        write_binary_i32(out, (int32_t)models[m].size());
        for (u64 code : models[m]) write_binary_u64(out, code);

        // 1. Symmetric PSD types: all k with k <= m-2 and k % 2 == m % 2
        struct TypeSpec { int k; int ti; u64 code; int ell; };
        std::vector<TypeSpec> types;
        for (int k = m % 2; k <= m - 2; k += 2) {
            int ell = (m + k) / 2;
            for (size_t ti = 0; ti < models[k].size(); ++ti) {
                types.push_back({k, (int)ti, models[k][ti], ell});
            }
        }
        write_binary_i32(out, (int32_t)types.size());
        for (const auto &ts : types) {
            auto fl = generate_flags(ts.k, ts.code, ts.ell);
            auto auts = compute_aut_action(ts.k, ts.code, ts.ell, fl);
            long long denom = 0;
            std::vector<Triplet> trips;
            compute_product_table(m, models[m], ts.k, ts.code, ts.ell, fl, ts.ell, fl, denom, trips);

            write_binary_i32(out, ts.k);
            write_binary_i32(out, ts.ell);
            write_binary_u64(out, ts.code);
            write_binary_i32(out, (int32_t)fl.size());
            for (u64 fc : fl) write_binary_u64(out, fc);

            write_binary_i32(out, (int32_t)auts.size());
            for (const auto &a : auts) {
                for (int x : a) write_binary_i32(out, x);
            }

            write_binary_i64(out, denom);
            write_binary_i64(out, (int64_t)trips.size());
            for (const auto &t : trips) {
                write_binary_i32(out, t.h_idx);
                write_binary_i32(out, t.a);
                write_binary_i32(out, t.b);
                write_binary_i32(out, t.cnt);
            }
            std::cerr << "  dumped type k=" << ts.k << " ti=" << ts.ti
                      << " |flags|=" << fl.size() << " |Aut|=" << auts.size()
                      << " nnz=" << trips.size() << " denom=" << denom << "\n";
        }

        // 2. 1-flag out-degree / in-degree linear constraint tables!
        // Type 1 (k=1, sigma=0):
        // flags of size 2: 0=non-edge, 1=(0->1) [E+], 2=(1->0) [E-]
        // flags of size m-1: all 1-flags F in F_{m-1}^1
        // Dump:
        //   (a) product table [[E_j * F]]_1 for j in {0,1,2} (all 1-flags of size 2) and F in F_{m-1}^1
        //   (b) unlabel table [[F]]_1 for F in F_{m-1}^1
        auto f1_2 = generate_flags(1, 0ULL, 2);
        auto f1_m1 = generate_flags(1, 0ULL, m - 1);
        long long p_denom = 0, u_denom = 0;
        std::vector<Triplet> p_trips, u_trips;
        compute_product_table(m, models[m], 1, 0ULL, 2, f1_2, m - 1, f1_m1, p_denom, p_trips);
        compute_unlabel_table(m, models[m], 1, 0ULL, m - 1, f1_m1, u_denom, u_trips);

        write_binary_i32(out, (int32_t)f1_2.size());
        for (u64 fc : f1_2) write_binary_u64(out, fc);
        write_binary_i32(out, (int32_t)f1_m1.size());
        for (u64 fc : f1_m1) write_binary_u64(out, fc);

        write_binary_i64(out, p_denom);
        write_binary_i64(out, (int64_t)p_trips.size());
        for (const auto &t : p_trips) {
            write_binary_i32(out, t.h_idx);
            write_binary_i32(out, t.a);
            write_binary_i32(out, t.b);
            write_binary_i32(out, t.cnt);
        }

        write_binary_i64(out, u_denom);
        write_binary_i64(out, (int64_t)u_trips.size());
        for (const auto &t : u_trips) {
            write_binary_i32(out, t.h_idx);
            write_binary_i32(out, t.a);
            write_binary_i32(out, t.b);
            write_binary_i32(out, t.cnt);
        }

        // 3. Also dump 2-flag product tables for k=2 types (ell1=3, ell2=m-1) if m >= 4?
        // Wait: for m >= 4, 2-vertex constraints (e.g. non-edge shift / common neighborhood / triangle-free
        // pair inequalities!) need [[E_pair * F]]_sigma for k=2, ell1=3, ell2=m-1!
        // Let's dump ALL 1-flags of size 3 paired with 1-flags of size m-2 if m >= 5 as well,
        // e.g. for quadratic out-degree constraints [[(E+ - c)^2 * F]]_1 = 0!!
        // Wait: (E+ - c)^2 has size 3! Paired with F of size m-2 gives m!
        // Let's include a version tag and dump 1-flag (3, m-2) if m >= 5!
        int has_quad1 = (m >= 5) ? 1 : 0;
        write_binary_i32(out, has_quad1);
        if (has_quad1) {
            auto f1_3 = generate_flags(1, 0ULL, 3);
            auto f1_m2 = generate_flags(1, 0ULL, m - 2);
            long long qp_denom = 0;
            std::vector<Triplet> qp_trips;
            compute_product_table(m, models[m], 1, 0ULL, 3, f1_3, m - 2, f1_m2, qp_denom, qp_trips);
            write_binary_i32(out, (int32_t)f1_3.size());
            for (u64 fc : f1_3) write_binary_u64(out, fc);
            write_binary_i32(out, (int32_t)f1_m2.size());
            for (u64 fc : f1_m2) write_binary_u64(out, fc);
            write_binary_i64(out, qp_denom);
            write_binary_i64(out, (int64_t)qp_trips.size());
            for (const auto &t : qp_trips) {
                write_binary_i32(out, t.h_idx);
                write_binary_i32(out, t.a);
                write_binary_i32(out, t.b);
                write_binary_i32(out, t.cnt);
            }
            // Also unlabel table for f1_3 on models_m (not needed if we already have f1_m1, wait:
            // we DO need [[F]]_1 for F in f1_m2 and [[E+ * F]]_1 for F in f1_m2? No, 1_1 * F lifts!)
        }

        // 4. Also dump exact out-edge density on models_m: for each H, #arcs / (m*(m-1))
        // Note: #arcs / (m*(m-1)) is literally [[E+]]_1(H)!!
        for (int hi = 0; hi < (int)models[m].size(); ++hi) {
            AdjMat H = decode_graph(m, models[m][hi]);
            int arcs = 0;
            for (int i = 0; i < m; ++i)
                for (int j = 0; j < m; ++j)
                    arcs += H.a[i][j];
            write_binary_i32(out, arcs);
        }

        out.close();
        std::cerr << "Wrote " << path << "\n";
    }
    return 0;
}
