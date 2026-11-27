// gen_canon_witnesses.cpp - Exact 1->2->3->4->5->6 canonical completeness witness generator
// for Lean 4 pure-kernel verification (ZERO native_decide, ZERO bv_decide!).
//
// Compiles with: g++ -O3 -march=native -fopenmp gen_canon_witnesses.cpp -o gen_canon_witnesses
//
// Outputs:
//   canon_witnesses_m6.json :
//     - models["1".."6"] : canonical uint64 codes matching flags_m4/m5/m6.bin index-for-index
//     - steps["2".."6"]  : array of |M_{k-1}| * 3^(k-1) entries, indexed by g * 3^(k-1) + ext:
//         * trit(ext, i) = (ext / 3^i) % 3 for i = 0..k-2:
//             0 = no arc between i and k-1
//             1 = arc i -> k-1
//             2 = arc k-1 -> i
//         * If extended graph G' has a C3:
//             [0, u, w]  where 0 <= u, w < k-1, u != w,
//             and G'.adj(u, w) && G'.adj(w, k-1) && G'.adj(k-1, u)  (canonical orientation!)
//         * If extended graph G' is C3-free:
//             [1, canon_idx, p0, p1, ..., p_{k-1}]  where perm = (p0..p_{k-1}) is a bijection on 0..k-1
//             satisfying: forall a, b in 0..k-1, G'.adj(perm[a], perm[b]) == M_k[canon_idx].adj(a, b)
//             i.e. G'.relabel(perm) == M_k[canon_idx] identically in Lean!
//
// Also performs 100% independent internal self-verification of all 79,806 witnesses AND
// cross-checks M_4, M_5, M_6 against flags_m4.bin, flags_m5.bin, flags_m6.bin if present!

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

static inline bool has_c3_full(const AdjMat &g) {
    for (int i = 0; i < g.n; ++i)
        for (int j = 0; j < g.n; ++j)
            if (g.a[i][j])
                for (int k = 0; k < g.n; ++k)
                    if (g.a[j][k] && g.a[k][i]) return true;
    return false;
}

// Find witness (u, w) with 0 <= u, w < last such that u -> w -> last -> u.
static inline bool find_c3_with_last(const AdjMat &g, int &out_u, int &out_w) {
    int last = g.n - 1;
    for (int u = 0; u < last; ++u) {
        if (!g.a[last][u]) continue;
        for (int w = 0; w < last; ++w) {
            if (g.a[u][w] && g.a[w][last]) {
                out_u = u;
                out_w = w;
                return true;
            }
        }
    }
    return false;
}

// Exact lexicographical minimum code over all permutations of 0..n-1 (for n <= 6),
// ALSO returning the achieving permutation perm[0..n-1] such that
// encode_permuted(g, perm) == best (i.e. g.relabel(perm) == decode(n, best)).
static inline u64 canonical_with_perm(const AdjMat &g, int *best_perm) {
    int n = g.n;
    int perm[8];
    for (int i = 0; i < n; ++i) perm[i] = i;
    u64 best = ~0ULL;
    do {
        u64 c = encode_permuted(g, perm);
        if (c < best) {
            best = c;
            for (int i = 0; i < n; ++i) best_perm[i] = perm[i];
        }
    } while (std::next_permutation(perm, perm + n));
    return best;
}

static void cross_check_flags_bin(const std::string &path, int expected_m, const std::vector<u64> &models) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        std::cerr << "[WARN] " << path << " not found; skipping cross-check.\n";
        return;
    }
    uint32_t magic = 0, m = 0, n_models = 0;
    in.read((char*)&magic, 4);
    in.read((char*)&m, 4);
    in.read((char*)&n_models, 4);
    assert(magic == 0x464C4147U);
    assert((int)m == expected_m);
    assert(n_models == models.size());
    std::vector<u64> file_codes(n_models);
    in.read((char*)file_codes.data(), n_models * sizeof(u64));
    for (size_t i = 0; i < models.size(); ++i) {
        if (file_codes[i] != models[i]) {
            std::cerr << "MISMATCH at m=" << expected_m << " idx=" << i
                      << ": file=" << file_codes[i] << " vs gen=" << models[i] << "\n";
            std::exit(1);
        }
    }
    std::cerr << "[OK] Cross-checked " << path << ": 100% byte-for-byte match (" << n_models << " models)!\n";
}

struct Witness {
    uint8_t is_free; // 0 = triangle witness (u, w), 1 = canonical isomorphism (canon_idx, perm)
    uint16_t val0;   // u or canon_idx
    uint16_t val1;   // w or unused
    uint8_t perm[8];
};

int main(int argc, char **argv) {
    std::string out_json = (argc > 1) ? argv[1] : "../certs/canon_witnesses_m6.json";
    std::string out_bin  = (argc > 2) ? argv[2] : "../certs/canon_witnesses_m6.bin";

    std::vector<std::vector<u64>> models(7);
    models[0] = {0ULL};
    models[1] = {0ULL};

    std::vector<std::vector<Witness>> steps(7);

    for (int k = 2; k <= 6; ++k) {
        const auto &prev = models[k - 1];
        int p3 = 1;
        for (int i = 0; i < k - 1; ++i) p3 *= 3;

        // First pass: collect canonical models M_k
        std::vector<u64> cand;
        #pragma omp parallel
        {
            std::vector<u64> local;
            #pragma omp for schedule(dynamic)
            for (size_t gi = 0; gi < prev.size(); ++gi) {
                AdjMat base = decode_graph(k - 1, prev[gi]);
                AdjMat g;
                g.n = k;
                int tmp_perm[8];
                for (int ext = 0; ext < p3; ++ext) {
                    memcpy(g.a, base.a, sizeof(base.a));
                    for (int i = 0; i < k; ++i) g.a[i][k - 1] = g.a[k - 1][i] = 0;
                    int x = ext;
                    for (int i = 0; i < k - 1; ++i) {
                        int s = x % 3;
                        x /= 3;
                        if (s == 1) g.a[i][k - 1] = 1;
                        else if (s == 2) g.a[k - 1][i] = 1;
                    }
                    int u, w;
                    if (!find_c3_with_last(g, u, w)) {
                        local.push_back(canonical_with_perm(g, tmp_perm));
                    }
                }
            }
            #pragma omp critical
            cand.insert(cand.end(), local.begin(), local.end());
        }
        std::sort(cand.begin(), cand.end());
        cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
        models[k] = std::move(cand);

        std::unordered_map<u64, uint16_t> code_to_idx;
        code_to_idx.reserve(models[k].size() * 2);
        for (size_t i = 0; i < models[k].size(); ++i) {
            code_to_idx[models[k][i]] = (uint16_t)i;
        }

        // Second pass: build exact witness table for every (g, ext)
        size_t total = prev.size() * (size_t)p3;
        steps[k].resize(total);
        std::vector<uint8_t> hit(models[k].size(), 0);
        size_t n_tri = 0, n_free = 0;

        #pragma omp parallel for schedule(dynamic) reduction(+:n_tri, n_free)
        for (size_t gi = 0; gi < prev.size(); ++gi) {
            AdjMat base = decode_graph(k - 1, prev[gi]);
            AdjMat g;
            g.n = k;
            int perm[8];
            for (int ext = 0; ext < p3; ++ext) {
                memcpy(g.a, base.a, sizeof(base.a));
                for (int i = 0; i < k; ++i) g.a[i][k - 1] = g.a[k - 1][i] = 0;
                int x = ext;
                for (int i = 0; i < k - 1; ++i) {
                    int s = x % 3;
                    x /= 3;
                    if (s == 1) g.a[i][k - 1] = 1;
                    else if (s == 2) g.a[k - 1][i] = 1;
                }
                Witness &wt = steps[k][gi * (size_t)p3 + (size_t)ext];
                memset(&wt, 0, sizeof(wt));
                int u = -1, w = -1;
                if (find_c3_with_last(g, u, w)) {
                    wt.is_free = 0;
                    wt.val0 = (uint16_t)u;
                    wt.val1 = (uint16_t)w;
                    ++n_tri;
                } else {
                    u64 c = canonical_with_perm(g, perm);
                    uint16_t cidx = code_to_idx.at(c);
                    wt.is_free = 1;
                    wt.val0 = cidx;
                    for (int i = 0; i < k; ++i) wt.perm[i] = (uint8_t)perm[i];
                    ++n_free;
                }
            }
        }

        // 100% INDEPENDENT SELF-VERIFICATION of every single witness!
        for (size_t gi = 0; gi < prev.size(); ++gi) {
            AdjMat base = decode_graph(k - 1, prev[gi]);
            AdjMat g;
            g.n = k;
            for (int ext = 0; ext < p3; ++ext) {
                memcpy(g.a, base.a, sizeof(base.a));
                for (int i = 0; i < k; ++i) g.a[i][k - 1] = g.a[k - 1][i] = 0;
                int x = ext;
                for (int i = 0; i < k - 1; ++i) {
                    int s = x % 3;
                    x /= 3;
                    if (s == 1) g.a[i][k - 1] = 1;
                    else if (s == 2) g.a[k - 1][i] = 1;
                }
                const Witness &wt = steps[k][gi * (size_t)p3 + (size_t)ext];
                if (wt.is_free == 0) {
                    int u = wt.val0, w = wt.val1;
                    assert(u >= 0 && u < k - 1 && w >= 0 && w < k - 1 && u != w);
                    assert(g.a[u][w] == 1 && g.a[w][k - 1] == 1 && g.a[k - 1][u] == 1);
                } else {
                    assert(!has_c3_full(g));
                    uint16_t cidx = wt.val0;
                    assert(cidx < models[k].size());
                    hit[cidx] = 1;
                    bool seen[6] = {false};
                    for (int i = 0; i < k; ++i) {
                        assert(wt.perm[i] < k && !seen[wt.perm[i]]);
                        seen[wt.perm[i]] = true;
                    }
                    AdjMat canon = decode_graph(k, models[k][cidx]);
                    for (int a = 0; a < k; ++a) {
                        for (int b = 0; b < k; ++b) {
                            assert(g.a[wt.perm[a]][wt.perm[b]] == canon.a[a][b]);
                        }
                    }
                }
            }
        }
        for (size_t i = 0; i < models[k].size(); ++i) assert(hit[i] == 1);

        std::cerr << "Step " << (k - 1) << "->" << k << ": |M_" << k << "|=" << models[k].size()
                  << ", total=" << total << " (c3_tri=" << n_tri << ", c3_free=" << n_free
                  << ") -- 100% SELF-VERIFIED!\n";
    }

    // Verify exact expected counts
    assert(models[1].size() == 1);
    assert(models[2].size() == 2);
    assert(models[3].size() == 6);
    assert(models[4].size() == 32);
    assert(models[5].size() == 317);
    assert(models[6].size() == 6583);

    cross_check_flags_bin("flags_m4.bin", 4, models[4]);
    cross_check_flags_bin("flags_m5.bin", 5, models[5]);
    cross_check_flags_bin("flags_m6.bin", 6, models[6]);

    // Write compact binary format (magic "CWIT" = 0x54495743)
    {
        std::ofstream bo(out_bin, std::ios::binary);
        uint32_t magic = 0x54495743U, ver = 1, max_k = 6;
        bo.write((char*)&magic, 4);
        bo.write((char*)&ver, 4);
        bo.write((char*)&max_k, 4);
        for (int k = 1; k <= 6; ++k) {
            uint32_t nm = (uint32_t)models[k].size();
            bo.write((char*)&nm, 4);
            bo.write((char*)models[k].data(), nm * sizeof(u64));
        }
        for (int k = 2; k <= 6; ++k) {
            uint32_t nt = (uint32_t)steps[k].size();
            bo.write((char*)&nt, 4);
            for (const auto &wt : steps[k]) {
                // Pack each witness into 12 bytes: is_free(1), pad(1), val0(2), val1(2), perm[6](6)
                uint8_t buf[12] = {0};
                buf[0] = wt.is_free;
                memcpy(buf + 2, &wt.val0, 2);
                memcpy(buf + 4, &wt.val1, 2);
                memcpy(buf + 6, wt.perm, 6);
                bo.write((char*)buf, 12);
            }
        }
        std::cerr << "Wrote binary witness table to " << out_bin << "\n";
    }

    // Write clean JSON format
    {
        std::ofstream jo(out_json);
        jo << "{\n";
        jo << "  \"format\": \"canon_witnesses_m6_v1\",\n";
        jo << "  \"encoding\": \"pair_idx(i,j)=i*(2*k-i-1)/2+(j-i-1), 2 bits: 0=none, 1=i->j, 2=j->i; trit(ext,i)=(ext/3^i)%3: 0=none, 1=i->k-1, 2=k-1->i; entry=[0,u,w] means u->w->(k-1)->u; entry=[1,cidx,p0..p_{k-1}] means G'.relabel(perm)==M_k[cidx]\",\n";
        jo << "  \"counts\": {\"1\": 1, \"2\": 2, \"3\": 6, \"4\": 32, \"5\": 317, \"6\": 6583},\n";
        jo << "  \"models\": {\n";
        for (int k = 1; k <= 6; ++k) {
            jo << "    \"" << k << "\": [";
            for (size_t i = 0; i < models[k].size(); ++i) {
                if (i) jo << ",";
                jo << models[k][i];
            }
            jo << "]" << (k < 6 ? "," : "") << "\n";
        }
        jo << "  },\n";
        jo << "  \"steps\": {\n";
        for (int k = 2; k <= 6; ++k) {
            jo << "    \"" << k << "\": [";
            for (size_t i = 0; i < steps[k].size(); ++i) {
                if (i) jo << ",";
                const auto &wt = steps[k][i];
                if (wt.is_free == 0) {
                    jo << "[0," << wt.val0 << "," << wt.val1 << "]";
                } else {
                    jo << "[1," << wt.val0;
                    for (int j = 0; j < k; ++j) jo << "," << (int)wt.perm[j];
                    jo << "]";
                }
            }
            jo << "]" << (k < 6 ? "," : "") << "\n";
        }
        jo << "  }\n";
        jo << "}\n";
        std::cerr << "Wrote JSON witness table to " << out_json << "\n";
    }

    return 0;
}
