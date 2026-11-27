# Triangle bounds for the Caccetta–Häggkvist conjecture

In a loopless digraph on $n\ge1$ vertices, minimum out-degree at least $0.3383n$ forces a directed cycle of length two or three. In an oriented graph the cycle has length three. This computer-assisted bound combines a mathematical reduction with exact integer checks of a six-vertex certificate. The strongest unconditional general bound in the Lean library is $427/1250=0.3416$. The conjectured threshold is $1/3$. [Proof and verification status](PROOF.md)

Hladký, Král’ and Norin proved the bound $0.3465$ and reported a six-vertex calculation at $0.3388$ by de Joannis de Verclos, Sereni and Volec. Samuel Burbulla’s public Lean project states an unconditional bound of $679/2000=0.3395$. [Hladký–Král’–Norin, concluding remarks](https://arxiv.org/pdf/0908.2791) · [Burbulla’s formalization](https://github.com/samuelburbulla/caccetta-haggkvist-bound)

## Results in the default Lean build

| Result | Hypotheses and conclusion | Source |
| --- | --- | --- |
| Five-vertex CH bound | $\delta^+(G) \ge (427/1250)n$ implies a digon or a directed triangle. | [Five-vertex interval theorem](lean/CaccettaHaggkvist/CertM5_427_1250.lean) |
| Feedback arc sets | If $G$ has neither a digon nor a directed triangle, $100\beta(G)\le 83\gamma(G)$. Here $\beta$ is the minimum number of arcs whose deletion makes $G$ acyclic and $\gamma$ counts unordered nonadjacent pairs. | [CSS bound and digraph wrapper](lean/CaccettaHaggkvist/CSS83.lean) |
| Exact one-third bound for a class of graphs | A directed-triangle-free oriented graph avoiding the four specified five-vertex patterns has a vertex $v$ with $3d^+(v)\le n-1$. The four finite obstructions in the source concern intermediate critical-arc claims. | [Patterns, theorem and witnesses](lean/CaccettaHaggkvist/RazborovSharp.lean) |
| Rainbow triangles | In a simple edge-colored graph on $n\ge1$ vertices, at least $n$ colors with each color class of size at least $(12457/31250)n = 0.398624n$ force a rainbow triangle. This uses the five-vertex CH theorem. | [Unconditional rainbow theorem](lean/CaccettaHaggkvist/RainbowBounds.lean) |
| Six-vertex coverage | Every directed-triangle-free oriented graph on six labeled vertices is a relabeling of a listed model. The extension step covers all $317\cdot 3^5=77{,}031$ ways to add a vertex to a five-vertex representative. | [Coverage of 6,583 models](lean/CaccettaHaggkvist/CanonCompleteness.lean) |

## Six-vertex certificate

The verifier forms integer Gram matrices from the SOS factors and evaluates each model at the two endpoints. The coefficient of each model is affine in the degree ratio, so negativity at both endpoints implies negativity on the whole interval.

| Order | Degree ratio or interval | Models | SOS factors (ordinary + weighted) | Largest model coefficient at the checked points |
| --- | --- | ---: | ---: | --- |
| 5 | $689/2000$ | 317 | 38 + 0 | $-1.882825\times10^{-6}$ |
| 5 | $[427/1250,689/2000]$ | 317 | 33 + 0 | $-5.779827\times10^{-7}$, $-6.388876\times10^{-7}$ |
| 6 | $[3383/10000,427/1250]$ | 6,583 | 1,445 + 48 | $-1.039745\times10^{-8}$, $-1.370979\times10^{-8}$ |
| 6 | $[677/2000,427/1250]$ | 6,583 | 1,320 + 0 | $-1.321500\times10^{-8}$, $-2.536671\times10^{-8}$ |

The maxima are rounded for display. The verification command prints the exact fractions. For each six-vertex certificate, a second calculation checks the extension witnesses and evaluates all 720 orderings of each of the 6,583 representatives directly from its adjacency relation. This gives the same endpoint maxima as the product-table calculation. The two six-vertex rows are alternative certificates with the same upper endpoint. [Certificate files](certs/) · [Direct evaluator](solver/verify_six_vertex.py)

The Lean theorem `hasCycleLe3_of_six_vertex_certificate` uses the five-vertex upper bound, the six-vertex classification, and finite extrema to close the interval. The weighted-flag lemma gives the conditional-mean identity and the error bound for one weighted square. Applying the interval theorem at $3383/10000$ still requires instantiating the graph functions with the certificate coefficients, assembling their expectation bound, and checking their symmetrized values on all representatives inside Lean. The rainbow result at $79697/200000 = 0.398485$ takes that stronger CH bound as an explicit hypothesis. [Six-vertex interval theorem](lean/CaccettaHaggkvist/IntervalM6Bridge.lean) · [Weighted flags](lean/CaccettaHaggkvist/WeightedFlags.lean) · [Rainbow reduction](lean/CaccettaHaggkvist/RainbowTriangle.lean)

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
