# Triangle bounds for the Caccetta–Häggkvist conjecture

If a loopless digraph on $n\ge1$ vertices has minimum out-degree at least $0.33823n$, it contains a directed cycle of length two or three. In an oriented graph the cycle is a triangle. Two exact six-vertex certificates give the sharper bound $c^*\le491353450461462518/1452728700789264675\approx0.3382279500601$ on the supremum of the minimum out-degree ratio of triangle-free oriented graphs. The strongest general CH threshold proved end to end in this repository's default Lean build is $3415403/10000000=0.3415403$. The conjectured threshold is $1/3$. [Proof and verification status](PROOF.md)

Hladký, Král’ and Norin proved the bound $0.3465$ and reported a six-vertex calculation at $0.3388$ by de Joannis de Verclos, Sereni and Volec. Samuel Burbulla’s public Lean project states an unconditional bound of $679/2000=0.3395$. [Hladký–Král’–Norin, concluding remarks](https://arxiv.org/pdf/0908.2791) · [Burbulla’s formalization](https://github.com/samuelburbulla/caccetta-haggkvist-bound)

## Results in the default Lean build

| Result | Hypotheses and conclusion | Source |
| --- | --- | --- |
| Five-vertex CH bound | $\delta^+(G) \ge (3415403/10000000)n$ implies a digon or a directed triangle. | [Five-vertex interval theorem](lean/CaccettaHaggkvist/CertM5Refined.lean) |
| Feedback arc sets | If $G$ has neither a digon nor a directed triangle, $1250\beta(G)\le1037\gamma(G)$. Here $\beta$ is the minimum number of arcs whose deletion makes $G$ acyclic and $\gamma$ counts unordered nonadjacent pairs. | [CSS bound and digraph wrapper](lean/CaccettaHaggkvist/CSS83.lean) |
| Exact one-third bound for a class of graphs | A directed-triangle-free oriented graph avoiding the four specified five-vertex patterns has a vertex $v$ with $3d^+(v)\le n-1$. For general triangle-free oriented graphs of minimum out-degree $d$, there are $k$ vertex-disjoint obstructions with $3d+1\le n+10k$. | [Four-pattern theorem](lean/CaccettaHaggkvist/RazborovSharp.lean) · [Packing bound](lean/CaccettaHaggkvist/PatternPacking.lean) |
| Rainbow triangles | In a simple edge-colored graph on $n\ge1$ vertices, at least $n$ colors with each color class of size at least $(199311/500000)n = 0.398622n$ force a rainbow triangle. This uses the five-vertex CH theorem. | [Unconditional rainbow theorem](lean/CaccettaHaggkvist/RainbowBounds.lean) |
| Six-vertex coverage | Every directed-triangle-free oriented graph on six labeled vertices is a relabeling of a listed model. The extension step covers all $317\cdot 3^5=77{,}031$ ways to add a vertex to a five-vertex representative. | [Coverage of 6,583 models](lean/CaccettaHaggkvist/CanonCompleteness.lean) |

## Six-vertex certificate

The verifier forms integer Gram matrices from the SOS factors and evaluates each model at the two endpoints. The coefficient of each model is affine in the degree ratio, so negativity at both endpoints implies negativity on the whole interval.

| Order | Degree ratio or interval | Models | SOS factors (ordinary + weighted) | Largest model coefficient at the checked points |
| --- | --- | ---: | ---: | --- |
| 5 | $689/2000$ | 317 | 38 + 0 | $-1.882825\times10^{-6}$ |
| 5 | $[427/1250,689/2000]$ | 317 | 33 + 0 | $-5.779827\times10^{-7}$, $-6.388876\times10^{-7}$ |
| 5 | $[3415403/10000000,689/2000]$ | 317 | 33 + 0 | $-3.16319\times10^{-10}$, $-6.388876\times10^{-7}$ |
| 6 | $[3383/10000,427/1250]$ | 6,583 | 1,445 + 48 | $-1.039745\times10^{-8}$, $-1.370979\times10^{-8}$ |
| 6 | $[677/2000,427/1250]$ | 6,583 | 1,320 + 0 | $-1.321500\times10^{-8}$, $-2.536671\times10^{-8}$ |
| 6 | $[33827/100000,427/1250]$ | 6,583 | 1,305 + 45 | $-5.16066\times10^{-9}$, $-8.37545\times10^{-9}$ |
| 6 | $[33823/100000,33827/100000]$ | 6,583 | 1,719 + 101 | $-3.36155\times10^{-9}$, $-3.75343\times10^{-9}$ |

The maxima are rounded here. The product-table verifier regenerates the flag counts, and an independent evaluator reconstructs each sum from adjacency with all 720 orderings and their multiplicities. Both verify the endpoint fractions for all four six-vertex certificates. The last two rows form the chain from $0.3416$ to $0.33823$. Extending the last certificate to its first zero gives the stated rational bound on $c^*$. [Exact margins and interval argument](PROOF.md#42-exact-certificate-margins) · [Direct evaluator](solver/verify_six_vertex.py)

The Lean certificate compiler encodes the actual flag coefficients, checks the Gram matrices against their signed integer factors, and derives the expectation inequality for the resulting program. The 35 Gram blocks at $0.3385$ and the 42 at $0.3383$ have all passed the kernel check. The outstanding step for those concrete Lean theorems is the kernel evaluation of the endpoint inequalities over all 6,583 representatives. The six-vertex numerical claims above use the external exact evaluations. [Compiler](solver/compile_six_vertex.py) · [Program soundness](lean/CaccettaHaggkvist/SixVertexProgram.lean) · [Finite check and CH theorem](lean/CaccettaHaggkvist/SixVertexBound.lean)

## Reproduce

With Git and the Elan toolchain manager installed, run the following from the repository root. The project pins Lean and Mathlib to 4.36.0. On an 11 GiB server the project builds with two Lean worker threads. A fresh project build can take tens of minutes.

```sh
cd lean
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build
lake env lean Audit.lean
```

From the repository root, regenerate the five- and six-vertex flag tables and run both certificate verifiers. This uses Bash, a C++17 compiler with OpenMP, and Python 3.9 or later. The script uses a temporary directory for the generated tables.

```sh
bash solver/verify_chain.sh
```

The script rebuilds the counting tables on the CPU, checks the rational certificates, and cross-checks the six-vertex coefficients directly from adjacency. The direct check also validates every extension witness. [Certificate checker](solver/verify_six_vertex.py) · [Witness generator](solver/gen_canon_witnesses.cpp)

To reproduce the 77 concrete Gram checks, run the following from the repository root. The compiler reads the flag identifiers and writes the certificate-specific Lean modules to Git-ignored directories.

```sh
work=$(mktemp -d)
g++ -std=c++17 -O3 -fopenmp solver/flag_gen.cpp -o "$work/flags"
g++ -std=c++17 -O3 -fopenmp solver/flag_gen_ext.cpp -o "$work/ext"
"$work/flags" dump 6 "$work"
"$work/ext" "$work/flags_m6.bin" "$work/ext_m6.bin"
python3 solver/compile_six_vertex.py certs/cert_m6_css83_nosos_677_2000_to_427_1250.json \
    "$work/flags_m6.bin" "$work/ext_m6.bin" lean/CaccettaHaggkvist Plain3385
python3 solver/compile_six_vertex.py certs/cert_m6_css83_sos_3383_10000_to_427_1250.json \
    "$work/flags_m6.bin" "$work/ext_m6.bin" lean/CaccettaHaggkvist Weighted3383
cd lean
LEAN_NUM_THREADS=2 lake --wfail build CaccettaHaggkvist.Plain3385.Valid CaccettaHaggkvist.Weighted3383.Valid
```

Each certificate also has a `Bridge` target proving the CH implication from the finite model checks, and a `Result` target that additionally requests all 6,583 kernel checks. The generated `Rows` modules check 12 representatives apiece by default. Lake can reuse completed modules across invocations. The geometry table is shared by all certificates.

## License

The project is distributed under the Apache License, Version 2.0. [License text](LICENSE)

## References

1. L. Caccetta and R. Häggkvist, *On minimal digraphs with given girth*, Proc. 9th S-E Conf. Combin., Graph Theory and Computing, Congr. Numer. **21** (1978), 181–187.
2. J. Shen, *Directed triangles in digraphs*, J. Combin. Theory Ser. B **74** (1998), 405–407.
3. P. Hamburger, P. Haxell, and A. Kostochka, *On directed triangles in digraphs*, Electron. J. Combin. **14** (2007), #N19.
4. M. Chudnovsky, P. Seymour, and B. Sullivan, *Cycles in dense digraphs*, Combinatorica **28** (2008), 1–18 [arXiv:math/0702147](https://arxiv.org/abs/math/0702147).
5. J. Hladký, D. Král', and S. Norin, *Counting flags in triangle-free digraphs*, Combinatorica **37** (2017), 49–76 [arXiv:0908.2791](https://arxiv.org/abs/0908.2791).
6. A. A. Razborov, *On the Caccetta–Häggkvist conjecture with forbidden subgraphs*, J. Graph Theory **74** (2013), 236–248 [arXiv:1107.2247](https://arxiv.org/abs/1107.2247).
7. K. Chen, S. Karson, D. Liu, and J. Shen, *On the Chudnovsky–Seymour–Sullivan conjecture on cycles in triangle-free digraphs*. [arXiv:0909.2468](https://arxiv.org/abs/0909.2468).
8. R. Aharoni, M. DeVos, and R. Holzman, *Rainbow triangles and the Caccetta–Häggkvist conjecture*, J. Graph Theory **92** (2019), 347–360.
9. P. Hompe, Z. Qu, and S. Spirkl, *Improved bounds for the triangle case of Aharoni’s rainbow generalization of the Caccetta–Häggkvist conjecture*, Discrete Math. **347** (2024), 113691. [Published article](https://doi.org/10.1016/j.disc.2023.113691).
10. S. Burbulla, *Caccetta–Häggkvist bound*. The public Lean project states an unconditional $679/2000$ bound. [Repository](https://github.com/samuelburbulla/caccetta-haggkvist-bound).
