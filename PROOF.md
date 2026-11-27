# Directed triangle bounds and certificate soundness

The default Lean build proves the five-vertex bound, the CSS and forbidden-pattern theorems, and a rainbow consequence. The six-vertex result uses an additional exact integer computation. The correspondence between that computation and the Lean graph functional is still an open formalization step.

## 1. Statements of Main Theorems

Let $G = (V, E)$ be a finite simple directed graph (`Digraph V`, irreflexive: $\neg (v \to v)$). Say $G$ is **3-free** (`¬ G.HasCycleLe3`) if it contains neither a digon ($u \to v \to u$) nor a directed triangle ($u \to v \to w \to u$); equivalently, $G$ is a **$\vec{C}_3$-free oriented graph** (`OrientedGraph V` with `G.TriangleFree`). Write $d^+(v) = |N^+(v)|$, $\delta^+(G) = \min_{v \in V} d^+(v)$, $\gamma(G)$ for the number of unordered non-adjacent pairs $\{u, v\} \subseteq V$ (so `G.ordNonEdges` $= 2\gamma(G)$), and $\beta(G)$ for the minimum size of a feedback arc set $F \subseteq E$ such that $G \setminus F$ is acyclic.

1. **Unconditional CH bound in Lean.** For every finite nonempty directed-triangle-free oriented graph $G$ on $n$ vertices,
   $$\delta^+(G)<(427/1250)n.$$
   The base certificate at $689/2000$ and the interval certificate down to $427/1250$ both have closed Lean theorems. Section 4 gives the additional six-vertex calculation at $3383/10000$. [Five-vertex interval theorem](lean/CaccettaHaggkvist/CertM5_427_1250.lean)

2. **Feedback arc sets.** Every finite 3-free digraph admits a feedback arc set of size $\beta(G)\le (83/100)\gamma(G)$. For nonempty graphs the degree corollary gives $100\delta^+(G)(\delta^+(G)+1)\le166\gamma(G)$. [CSS theorem and corollaries](lean/CaccettaHaggkvist/CSS83.lean)

3. **Forbidden patterns.** A finite nonempty directed-triangle-free oriented graph avoiding $P_1,P_2,P_3,P_4$ has a vertex $v$ with $3d^+(v)\le n-1$. Each obstruction in Section 5 violates a specified intermediate critical-arc claim when one prohibition is removed. [Four-pattern theorem](lean/CaccettaHaggkvist/RazborovSharp.lean)

4. **Rainbow triangles.** At least $n$ color classes of size at least $(12457/31250)n$ in a simple edge-colored graph on $n\ge1$ vertices force a rainbow triangle. This follows in Lean from the five-vertex CH bound. The specialization at $79697/200000$ takes the stronger CH bound at $3383/10000$ as an explicit argument. [Unconditional corollary](lean/CaccettaHaggkvist/RainbowBounds.lean) · [Parameterized reduction](lean/CaccettaHaggkvist/RainbowTriangle.lean)

---

## 2. Exact Finite-to-Flag-Algebra Bridge (Zero Limits, Zero $O(1/n)$ Loss)

Formalized in [WeightBridge.lean](lean/CaccettaHaggkvist/WeightBridge.lean), [FlagCert.lean](lean/CaccettaHaggkvist/FlagCert.lean), and [ExtremalBridge.lean](lean/CaccettaHaggkvist/ExtremalBridge.lean).

### 2.1 Theorem B1 (Deterministic Finite $\varepsilon$-Extremal i.i.d. Sampling)

Define the global supremum over all finite nonempty simple $\vec{C}_3$-free oriented graphs:
$$c^* := \sup \left\{ \frac{\delta^+(H)}{|V(H)|} \;\middle|\; H \text{ finite nonempty simple } \vec{C}_3\text{-free oriented graph} \right\} \in \left[\tfrac{1}{3}, 1\right].$$
Given any $\varepsilon > 0$, choose a finite nonempty $\vec{C}_3$-free oriented graph $G_1$ with $\delta^+(G_1)/|V(G_1)| > c^* - \varepsilon$. Setting $d_0 := \delta^+(G_1)$ and deleting $\deg^+_{G_1}(v) - d_0$ arbitrary outgoing arcs from each $v \in V(G_1)$ yields a finite simple $\vec{C}_3$-free oriented graph $G_0$ on $n := |V(G_1)| \ge 1$ vertices that is **exact $d_0$-out-regular**, with ratio $c_0 := d_0 / n \in (c^* - \varepsilon,\, c^*]$.

Sample $(x_1, \dots, x_m) \sim \mathrm{Unif}(V^m)$ **i.i.d. with replacement**, and let $G_0[x_1, \dots, x_m]$ be the oriented graph on $[m]$ placing arc $i \to j$ iff $x_i \to_{G_0} x_j$ (note that since $G_0$ is loopless, colliding indices $x_i = x_j$ automatically produce a non-edge, and every realization is a blow-up induced subgraph of $G_0$, hence always $\vec{C}_3$-free). Setting $p_H := \mathbb{P}[G_0[x_1, \dots, x_m] \cong H]$ for $H \in \mathcal{F}_m$ avoids all infinite flag-algebra limits, measure theory, and $O(1/n)$ error terms:

1. **Exact Cauchy–Schwarz (Class 2)**: Conditioned on $\mathbf{v} = (x_1, \dots, x_k) \in V^k$, disjoint free blocks $(x_{k+1}, \dots, x_\ell)$ and $(x_{\ell+1}, \dots, x_{2\ell-k})$ are independent and identically distributed $\mathrm{Unif}(V)$. Hence for every type $\sigma$ ($|\sigma| = k$, $2\ell - k \le m$) and vector $a \in \mathbb{R}^{\mathcal{F}^\sigma_\ell}$,
   $$\sum_{i,j} a_i a_j\, p([\![ F_i \cdot F_j ]\!]_\sigma) = \mathbb{E}_{\mathbf{v} \sim \mathrm{Unif}(V^k)}\!\left[\mathbf{1}_{\mathbf{v} \cong \sigma} \left(\sum_i a_i \, p_{\mathbf{v}}(F_i)\right)^2\right] \ge 0.$$
2. **Exact Out-Regularity (Class 1)**: For every $v \in V$, $\mathbb{P}_{y \sim \mathrm{Unif}(V)}[v \to y] = d_0 / n = c_0$ identically, so $p([\![ f \cdot (\alpha - c_0) ]\!]_\lambda) = 0$ for all $f \in \mathcal{F}^\lambda_{m-1}$.
3. **In-degree can vary.** Even under minimum-order vertex-weight criticality ($A w^* = c_0 \mathbf{1}$ and $A^T y^* = c_0 \mathbf{1}$ with full support), $y^* \ne w^*$ in general: the 6-vertex $\vec{C}_3$-free graph `Asym6` ($\{0\to 1, 0\to 2, 1\to 3, 2\to 4, 3\to 5, 4\to 5, 5\to 0\}$) with $w = (0.20, 0.05, 0.15, 0.20, 0.20, 0.20)$ has exact out-weight $0.20$ at every vertex but in-weights $(0.20, 0.20, 0.20, 0.05, 0.15, 0.40)$. Thus we never inject in-regularity into the general CH SDP.

### 2.2 Theorem C1 (Pointwise & SOS-Weighted Generalized Induction)

For any type $\sigma$ of size $k$, let $F_0(\sigma) \in \mathcal{F}^\sigma_{k+1}$ have free vertex $x$ receiving arcs from all $k$ roots ($v_i \to x$ for all $i \in [k]$), let $s^*(\sigma)$ be the sum of all other $\sigma$-flags of order $k + 1$ with no arc from $x$ to any root ($x \not\to v_i$), and set
$$f(\sigma) := s^*(\sigma) + c_0 F_0(\sigma) - c_0 \cdot 1_\sigma \in \mathcal{A}^\sigma_{k+1}.$$
For any $\mathbf{v} = (v_1, \dots, v_k) \in V^k$ inducing $\sigma$, let $U(\mathbf{v}) := \bigcap_{i=1}^k N^+_{G_0}(v_i)$ (automatically disjoint from $\{v_1, \dots, v_k\}$ by looplessness).
- Whenever $U(\mathbf{v}) \ne \emptyset$, $G_0[U(\mathbf{v})]$ is a finite nonempty $\vec{C}_3$-free oriented graph, so by definition of $c^*$ some $w \in U(\mathbf{v})$ has $|N^+(w) \cap U(\mathbf{v})| \le c^* |U(\mathbf{v})| \le (c_0 + \varepsilon)|U(\mathbf{v})|$. Every $x \in N^+(w)$ satisfies $x \not\to v_i$ (else $v_i \to w \to x \to v_i$ is a $\vec{C}_3$) and $x \notin \{v_1, \dots, v_k\}$ (else digon). Hence $c_0 n = |N^+(w)| \le (c_0 + \varepsilon)|U(\mathbf{v})| + |\mathrm{Src}^*(\mathbf{v})|$, giving
  $$f(\sigma)(\mathbf{v}) \ge -\varepsilon \cdot F_0(\sigma)(\mathbf{v}) \ge -\varepsilon.$$
- **Sink types** ($\exists r \in [k], \forall i \ne r,\, i \to r$): even when $U(\mathbf{v}) = \emptyset$, $N^+(v_r) \subseteq \mathrm{Src}^*(\mathbf{v})$, so $s^*(\sigma)(\mathbf{v}) \ge c_0$ and $f(\sigma)(\mathbf{v}) \ge -\varepsilon$ **unconditionally** for every $\mathbf{v} \cong \sigma$!
- **Non-sink types**: lifting to $\sigma^+ := F_0(\sigma)$ of size $k + 1$ witnesses $U(\mathbf{v}) \ne \emptyset$, giving $\pi^{\sigma^+,[k]}(f(\sigma))(\mathbf{v}, v_{k+1}) \ge -\varepsilon$ unconditionally!

This yields both **linear flag-multiplied cones** $[\![ g \cdot f(\sigma) ]\!]_\sigma \ge -\varepsilon [\![ g ]\!]_\sigma$ and **SOS-weighted induction PSD cones** $[\![ f(\sigma) \cdot h^2 ]\!]_\sigma \ge -\varepsilon [\![ h^2 ]\!]_\sigma$.

### 2.3 Theorem C2 (Pointwise Rational-Linearized CSS / HHK Bound)

Let $\chi(\sigma) \in \mathcal{A}^\sigma_{k+2}$ sum all $\sigma$-flags of order $k + 2$ where both free vertices $x, y$ lie in $U(\mathbf{v})$ and are non-adjacent ($x \not\sim y$). Under i.i.d. vertex sampling,
$$\chi(\sigma)(\mathbf{v}) = \frac{2\gamma(G_0[U(\mathbf{v})]) + |U(\mathbf{v})|}{n^2} \ge \frac{2\gamma(G_0[U(\mathbf{v})])}{n^2}$$
(the diagonal collision term $+|U|/n^2 \ge 0$ has the **favorable sign**!). By Theorem 2 ($\beta(H) \le \alpha_{\mathrm{CSS}}\gamma(H)$) and the Hamburger–Haxell–Kostochka feedback-arc-set out-degree bound ($\delta^+(H)^2 \le 2\alpha_{\mathrm{CSS}}\gamma(H)$), whenever $U(\mathbf{v}) \ne \emptyset$ some $w \in U(\mathbf{v})$ satisfies $|N^+(w) \cap U(\mathbf{v})| \le \sqrt{2\alpha_{\mathrm{CSS}}\gamma(G_0[U(\mathbf{v})])}$, yielding
$$s^*(\sigma)(\mathbf{v}) + \sqrt{\alpha_{\mathrm{CSS}}\,\chi(\sigma)(\mathbf{v})} \ge c_0 \qquad (\text{ZERO } \varepsilon \text{ error!}).$$
Applying AM-GM $\sqrt{X} \le \frac{X}{2r} + \frac{r}{2}$ at any rational tangent $r \in \mathbb{Q}_{>0}$ and multiplying by $2r$ yields the **100% rational affine-in-$c_0$ flag inequality**:
$$g_{\mathrm{CSS}}(\sigma, r) := \alpha_{\mathrm{CSS}}\,\chi(\sigma) + 2 r\, s^*(\sigma) + (r^2 - 2 c_0 r)\cdot 1_\sigma \ge 0$$
(unconditional for sink types, lifted to $\sigma^+$ for non-sink types), generating both linear flag-multiplied cones and SOS-weighted CSS PSD cones $[\![ g_{\mathrm{CSS}}(\sigma, r) \cdot h^2 ]\!]_\sigma \ge 0$.

### 2.4 Two-Endpoint Affine Interval Closure (`hasCycleLe3_of_interval_certificate`)

Every single constraint in Classes 1–4 is **affine (degree $\le 1$) in $c_0$**! Therefore, for any fixed rational certificate $(Q_\sigma, Q^{\mathrm{ind}}_\sigma, Q^{\mathrm{css}}_\sigma, y_f, \mu_i, \nu_j)$, every model slack $S_H(c_0) = u_H + c_0 v_H$ is affine in $c_0$. Verifying
$$\max_{H \in \mathcal{F}_m} S_H(c_{\mathrm{low}}) \le -\delta < 0 \qquad\text{and}\qquad \max_{H \in \mathcal{F}_m} S_H(c_{\mathrm{high}}) \le -\delta < 0$$
implies $S_H(c)\le-\delta$ throughout the closed interval. For the normalized permutation average let $B=\max_H |v_H|$, and let $M$ bound the expected induction loss by $M\varepsilon$. If $c^*\in[c_{\rm low},c_{\rm high}]$, an extremal sample has $c^*-\varepsilon<c_0\le c^*$. It follows that $S_H(c_0)\le -\delta+B\varepsilon$, even if $c_0<c_{\rm low}$. Choose $\varepsilon=\delta/[2(M+B+1)]$. Averaging gives $-M\varepsilon\le-\delta+B\varepsilon$, a contradiction. In Lean, `symPerm` sums over all permutations, so its expectation is scaled by $m!$. The six-vertex bridge obtains the common margin and slope bound by finite extrema. [Interval proof](lean/CaccettaHaggkvist/ExtremalBridge.lean) · [Six-vertex specialization](lean/CaccettaHaggkvist/IntervalM6Bridge.lean)

---

## 3. Chudnovsky–Seymour–Sullivan feedback bound

The formal proof constructs a feedback set together with a topological ranking of the remaining arcs. [CSS83.lean](lean/CaccettaHaggkvist/CSS83.lean)

### 3.1 The $\vec{C}_3$-Exclusion Non-Edge Lemma

Fix a finite simple $\vec{C}_3$-free oriented graph $H = (V, E)$ and $v \in V$. Partition $V \setminus \{v\} = A \sqcup B \sqcup C$ where $A = N^+(v)$, $B = N^-(v)$, $C = N^0(v)$ (note $e(A, B) = 0$ by $\vec{C}_3$-freeness). For each $u \in C$, set $K(u) := \{a \in A : a \to u\}$ ($k_u = |K(u)|$), $L(u) := \{b \in B : u \to b\}$ ($l_u = |L(u)|$), $q_A(u) := \bar{e}(A, u)$, $q_B(u) := \bar{e}(B, u)$.

> **Lemma ($\vec{C}_3$-Exclusion Non-Edge Bound).** *For every arc $u \to w$ inside $H[C]$:*
> $$q_A(w) \ge k_u - k_w \qquad\text{and}\qquad q_B(u) \ge l_w - l_u.$$
> *Proof.* For any $a \in K(u)$ ($a \to u$), $w \to a$ is forbidden (else $a \to u \to w \to a$ is $\vec{C}_3$), so $K(u) \subseteq K(w) \cup \{a \in A : a \perp w\}$, giving $k_u \le k_w + q_A(w)$. Symmetrically, for any $b \in L(w)$ ($w \to b$), $b \to u$ is forbidden (else $u \to w \to b \to u$ is $\vec{C}_3$), so $L(w) \subseteq L(u) \cup \{b \in B : b \perp u\}$, giving $l_w \le l_u + q_B(u)$. $\blacksquare$

### 3.2 Proof of $100\,\beta(H) \le 83\,\gamma(H)$ (`exists_feedback_200_card_le_83_ordNonEdges`)

Proceed by strong induction on $|V|$ ($|V| \le 1$ is trivial). For any $v \in V$ and partition $C(v) = C_A \sqcup C_B$, deleting $v$ and splitting into $H_1 = H[A \cup C_A]$ and $H_2 = H[B \cup C_B]$ loses all arcs from $H_1$ to $H_2$ — count $\tau(C_A, C_B) = e(A, C_B) + e(C_A, B) + e(C_A, C_B)$ — while saving all cross non-edges $\rho(C_A, C_B) = |C| + \bar{e}(A, B) + \bar{e}(A, C_B) + \bar{e}(B, C_A) + \bar{e}(C_A, C_B)$. Assume for contradiction that for every $v \in V$ and every partition $C(v) = C_A \sqcup C_B$,
$$\rho(C_A, C_B) < \frac{100}{83}\,\tau(C_A, C_B). \tag{*}$$

1. **Step 1 (Convex Step-1 Mixing, $\theta = \frac{17}{20}$)**: Let $c_v = |C(v)|$, $g_v = \bar{e}(A(v), B(v))$, $t_v = |E(H[C(v)])|$. Using the exact global triple-counting identities $\sum_v e(A, C) = \sum_v e(C, B) = \sum_v g_v$ and $\sum_v (\bar{e}(A, C) + \bar{e}(B, C)) = 2 \sum_v t_v$:
   - Averaging $(*)$ uniformly over all $2^{c_v}$ partitions of $C(v)$ and summing over $v \in V$ gives $\sum_v \left(c_v + \frac{c_v(c_v - 1)}{4} + \frac{33}{166} t_v - \frac{17}{83} g_v\right) < 0$.
   - Averaging $(*)$ over the two trivial partitions $(\emptyset, C)$ and $(C, \emptyset)$ gives $\sum_v \left(c_v + t_v - \frac{17}{83} g_v\right) < 0$.
   - Taking $\frac{17}{20} \cdot (\text{Uniform}) + \frac{3}{20} \cdot (\text{Trivial})$ and dropping $\frac{63}{80} c_v \ge 0$ yields a vertex $v \in V$ with $c := c_v \ge 1$ satisfying:
     $$g := \frac{g_v}{c^2} > \frac{83}{80} + \frac{1059}{680}\,t, \qquad t := \frac{t_v}{c^2}. \tag{1}$$
2. **Step 2 ($\lambda = \frac{3}{2}$ Threshold Partition & Branch-Free $\vec{C}_3$-Exclusion)**: Set $m_u = \min(k_u, l_u)$, $s_u = \max(k_u, l_u)$ (note $c\,g_v \ge \sum_{u \in C} m_u s_u$ by counting $a \perp b$ over $a \in K(u), b \in L(u)$ — since $a \to u \to b$ forces $a \perp b$!). Partition $C = U \sqcup W$ with $U = \{u \in C : 2 s_u \le 3 m_u\}$, $W = \{w \in C : 2 s_w > 3 m_w\}$, and split $W = W_A \sqcup W_B$ greedily ($W_A = \{k_w \ge l_w\}$, $W_B = \{l_w > k_w\}$). Define $a = |U|/c$, $x = \frac{1}{c^2}(\sum_{u \in U} \frac{k_u + l_u}{2} + \sum_{w \in W} m_w)$, $q_W = (\bar{e}(B, W_A) + \bar{e}(A, W_B))/c^2$, $t_1 = |E(H[U])|/c^2$, $t_2 = (e(U, W) + e(W, U))/c^2 \le a(1-a)$, $t_3 = |E(H[W])|/c^2$, and $m_3 = e(W_A, W_B)/c^2 \le t_3$.
   For every backward arc $w_1 \to w_2$ ($w_1 \in W_A, w_2 \in W_B$), the $\vec{C}_3$-Exclusion Non-Edge Lemma gives
   $$q_B(w_1) + q_A(w_2) \ge (k_{w_1} - l_{w_1}) + (l_{w_2} - k_{w_2}) = (s_{w_1} - m_{w_1}) + (s_{w_2} - m_{w_2}).$$
   Setting $\alpha_w := d^+(w, W_B)/c \in [0, 1]$ for $w \in W_A$ and $d^-(w, W_A)/c \in [0, 1]$ for $w \in W_B$ (so $\frac{1}{c}\sum_{w \in W} \alpha_w = 2 m_3$), summing over all arcs $W_A \to W_B$ and using $|W_A|, |W_B| \le c$ (completely branch-free, zero division by $|W_A|$ or $|W_B|$!) gives
   $$q_W \ge \frac{1}{c}\sum_{w \in W} \alpha_w\,\frac{s_w - m_w}{c}. \tag{2}$$
3. **Step 3 (Per-Vertex Rational Perfect Squares — Zero $\sqrt{\cdot}$)**: With $\beta_g = \frac{12}{25}$,
   - On $u \in U$ ($y_u = \frac{m_u + s_u}{2c}$, $2s_u \le 3m_u \implies \frac{m_u s_u}{c^2} \ge \frac{24}{25} y_u^2$): $\frac{288}{625}(y_u - \frac{15625}{11952})^2 \ge 0$ gives $\frac{100}{83} y_u \le \frac{12}{25}\frac{m_u s_u}{c^2} + \frac{197}{250}$.
   - On $w \in W$ ($z_w = \frac{m_w}{c}$, $\frac{m_w s_w}{c^2} \ge \frac{3}{2} z_w^2$, $\frac{s_w - m_w}{c} \ge \frac{1}{2} z_w$): perfect squares at $\alpha = 0$ and $\alpha = 1$ convexly combined by $\alpha_w \in [0, 1]$ yield $\frac{12}{25}\frac{m_w s_w}{c^2} - \frac{100}{83} z_w + \alpha_w \frac{s_w - m_w}{c} \ge -\frac{101}{200} + \frac{33}{100}\alpha_w$.
   - Summing over $C$ and applying $c\,g_v \ge \sum m_u s_u$ and (2) gives:
     $$g - \frac{100}{83}\,x + q_W \ge \frac{13}{25}\,g - \frac{197}{250}\,a - \frac{101}{200}(1 - a) + \frac{33}{50}\,m_3. \tag{3}$$
4. **Step 4 (Cut 3 ONLY — Strictly Positive-Definite Quadratic Contradiction)**: Applying **Cut 3** (uniform $\frac{1}{2}$-$\frac{1}{2}$ on $U$, greedy $W_A \subseteq C_A, W_B \subseteq C_B$ on $W$) while retaining $q_W$ gives
   $$g - \frac{100}{83}\,x + q_W < \frac{133}{166}\,t_1 + \frac{183}{166}\,t_2 + \frac{100}{83}\,m_3 - \frac{a^2}{4} - \frac{a(1-a)}{2}.$$
   Substituting (3) and (1) eliminates $t_1, t_3, m_3$ with nonnegative slacks ($+\frac{12161}{1411000}t_1 \ge 0$, $+\frac{13767}{17000}(t_3 - m_3) + \frac{373921}{1411000}m_3 \ge 0$) and bounds $t_2 \le a(1-a)$, collapsing directly to:
   $$0 > \frac{60089}{1411000}\,a^2 - \frac{26663}{352750}\,a + \frac{69}{2000} \ge \frac{162880399}{169571158000} > 0 \qquad (\forall\,a \in \mathbb{R}),$$
   a contradiction! $\blacksquare$

---

## 4. Exact six-vertex certificates

### 4.1 Coverage of the canonical list

Start with the unique one-vertex graph. To extend a graph by one vertex, independently choose for each old vertex an incoming arc, an outgoing arc, or no arc. Each stored witness gives either a directed triangle in this extension or a relabeling onto one of the next representatives. Induction therefore covers every directed-triangle-free oriented graph through order six. [Kernel proof](lean/CaccettaHaggkvist/CanonCompleteness.lean) · [Extension witnesses](certs/canon_witnesses_m6.json)

| Order | Listed representatives | Extensions checked | Triangle witnesses | Relabeling witnesses |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 2 | 3 | 0 | 3 |
| 3 | 6 | 18 | 1 | 17 |
| 4 | 32 | 162 | 26 | 136 |
| 5 | 317 | 2,592 | 766 | 1,826 |
| 6 | 6,583 | 77,031 | 33,001 | 44,030 |

### 4.2 Exact certificate margins

The independent checker constructs $Q=\sum_j w_j u_j u_j^\top$ with integer vectors and positive integer weights. It clears positive denominators and tests a strict integer inequality on every model. The vanilla certificate checks the fixed ratio $689/2000$. Regularization in `hasCycleLe3_of_flag_certificate` extends its conclusion to larger minimum degrees. The interval certificates each check both endpoints. [Vanilla soundness](lean/CaccettaHaggkvist/FlagCert.lean) · [Reproduction command](solver/verify_chain.sh)

| Certificate | Models | Exact maximum at low endpoint | Exact maximum at high endpoint |
| --- | ---: | ---: | ---: |
| [Five vertices, 689/2000](certs/cert_m5_689_2000.json) | 317 | $-3765649368533/2000000000000000000$ | fixed ratio |
| [Five vertices, 427/1250 to 689/2000](certs/cert_m5_tier1_linonly_427_1250_to_689_2000.json) | 317 | $-41890781053/72477573120000000$ | $-4630502621/7247757312000000$ |
| [Six vertices, 3383/10000 to 427/1250](certs/cert_m6_css83_sos_3383_10000_to_427_1250.json) | 6,583 | $-2057781171829/197912092999680000000$ | $-2035000603313/148434069749760000000$ |
| [Six vertices, 677/2000 to 427/1250](certs/cert_m6_css83_nosos_677_2000_to_427_1250.json) | 6,583 | $-523081657313/39582418599936000000$ | $-941320844407/37108517437440000000$ |

### 4.3 What the six-vertex Lean theorem requires

The direct evaluator checks each one-vertex extension witness. It then reads the flag identifiers and block order, skips the stored product counts, and evaluates the graph functions from adjacency on every permutation of each representative. Averaging over these permutations gives the table in §4.2. [Direct evaluator](solver/verify_six_vertex.py)

For a fixed ordering, write $c$ for the candidate out-degree ratio. The evaluator sums the following four contributions and divides by the common positive coefficient scale `q_denom`.

| Term | Contribution on one ordering |
| --- | --- |
| Out-degree | $\lambda(F)(\mathbf1_{v_0\to v_5}-c)$, where $F$ reads positions $0,\ldots,4$. |
| Ordinary SOS | $w\,u(F_L)u(F_R)$ on the prescribed root type. The two flags share their roots and have disjoint free positions. |
| Localized induction | A linear flag multiplier or an SOS product times $\mathbf1_{s^*}+c(\mathbf1_{F_0}-1)$. The localizer uses the last position. |
| Localized CSS | A linear flag multiplier or an SOS product times $\alpha\mathbf1_\chi+2r\mathbf1_{s^*}+r^2-2rc$. The localizer uses the last two positions. |

A flag contributes zero outside its root type. The evaluator checks that every active induction or CSS type has either a sink among its original roots or a root witnessing a common out-neighbor. The indicators and the corresponding conditional inequalities are defined in §§2.2–2.3.

Condition on the ordered roots. If the local inequality has mean at least $-\varepsilon$ and a flag factor has coefficients bounded by $b$ in absolute value, a weighted square with coefficient $w\ge0$ loses at most $w b^2\varepsilon$. Summing those losses and the linear induction multipliers gives a valid $M$. For the $3383/10000$ certificate, in the normalized permutation average, the direct evaluator gives

$$
M=\frac{1220442252361}{4398046511104},\qquad
B=\max_H |v_H|=\frac{8331737176489}{1099511627776000},\qquad
\varepsilon=\frac{2057781171829}{508663414095386040000}.
$$

With these values the two bounds in §2.4 contradict each other for $c^*\ge3383/10000$. This gives the computer-assisted bound $\delta^+(G)<(3383/10000)n$ for nonempty directed-triangle-free oriented graphs, using the externally evaluated rational inequalities. For a general loopless digraph the same degree condition forces a directed cycle of length two or three.

`WeightedFlag.expectation_eq` and `WeightedFlag.expectation_ge` formalize the conditional-mean identity and loss estimate for one localized square. The remaining concrete Lean instance of `hasCycleLe3_of_six_vertex_certificate` must encode the coefficients in $U,V$, assemble the expectation proof `hmean`, and prove the endpoint inequalities `hends` for those same functions. The bridge supplies the five-vertex upper endpoint, relabeling argument, uniform margin, and slope bound. [Weighted-square lemmas](lean/CaccettaHaggkvist/WeightedFlags.lean) · [Six-vertex bridge](lean/CaccettaHaggkvist/IntervalM6Bridge.lean)

---

## 5. The one-third bound under four five-vertex exclusions

The four-pattern result also recovers the earlier forbidden-subgraph bound. [Four-pattern proof](lean/CaccettaHaggkvist/RazborovSharp.lean) · [Three-pattern proof](lean/CaccettaHaggkvist/RazborovExact.lean)

### 5.1 The four partial five-vertex patterns

For an oriented graph $G$, write $a \to b$ for `G.adj a b` and $a \perp b$ for $a \ne b \land \neg(a \to b) \land \neg(b \to a)$. Define:
1. **$P_1$ (`HasPattern1`, 2 five-graphs: $F_5^{(1)}$ and $T_5^{(1)}$)**: $v \to w, v \to x, v \to z, w \to x, w \to y, y \to x, x \to z$ with $v \perp y, w \perp z, y \ne z$. (Every $\vec{C}_3$-free instance contains $F_5^{(1)} \supset \mathrm{IP}$ or $T_5^{(1)} \supset \mathrm{TC}$.)
2. **$P_2$ (`HasPattern2`, 3 five-graphs)**: $u \to v, u \to w, u \to z, v \to w, v \to x, w \to z$ with $u \perp x, v \perp z, w \perp x, x \ne z$. (Every instance contains $\mathrm{OP}$ on $\{u, v, w, x\}$.)
3. **$P_3$ (`HasPattern3`, 5 five-graphs, 1 overlapping $P_2 \implies 4$ new)**: $u \to v, u \to v', u \to x, v \to w, v' \to w, v' \to x$ with $v \ne v', u \perp w, x \perp w, \neg(v \to x)$. (Every instance contains $\mathrm{OP}$ on $\{u, v', x, w\}$.)
4. **$P_4$ (`HasPattern4`, `TC⁺`, 7 five-graphs)**: $u \to v \to w \to x, u \to x, x \to y$ with $u \perp w, v \perp x, v \ne y, \neg(v \to y \land w \to y), \neg(u \to y \land w \to y)$. (Every instance contains $\mathrm{TC}$ on $\{u, v, w, x\}$.)

Together $P_1 \cup P_2 \cup P_3 \cup P_4$ comprises exactly **`16 / 317 = 5.05%`** of $\mathcal{F}_5$, and every single one of those 16 graphs contains at least one of $\{\mathrm{TC}, \mathrm{OP}, \mathrm{IP}\}$.

### 5.2 Complete Proof of Theorem 3 (`exists_outDeg_le_third_of_forb_4patterns`)

Proceed by strong induction on $n = |V|$. Assume for contradiction that $3 d^+(u) \ge n$ for all $u \in V$ (`hdeg`), while every proper nonempty induced subgraph $S \subsetneq V$ satisfies the inductive bound `ih`. Call an arc $u \to v$ **critical** (`IsCritArc u v`) if $o(u, v) := |N^+(u) \cap N^+(v)|$ is minimized over $v \in N^+(u)$.

- **Helper (`exists_diff_out_of_crit`)**: Whenever $a \to b$ is critical and $c \in N^+(a) \cap N^+(b)$, since $c \notin N^+(a) \cap N^+(c)$ and $o(a, b) \le o(a, c)$, there exists $z \in (N^+(a) \cap N^+(c)) \setminus (N^+(a) \cap N^+(b))$ with $b \perp z$ (since $b \to c \to z$ forbids $z \to b$).
- **Claim 1 (`sharp_claim1`)**: For critical $v \to w$, no $x, y$ satisfy $v \to x, w \to x, w \to y, y \to x, v \perp y$. *Proof*: Apply the helper to $(v, w, x)$ to get $z \in (N^+(v) \cap N^+(x)) \setminus (N^+(v) \cap N^+(w))$ with $w \perp z$ and $y \ne z$; then $\{v, w, x, y, z\} \in P_1$. $\square$
- **Claim 2 (`sharp_claim2`)**: Every critical $v \to w$ has $x \in N^+(w)$ with $v \perp x$. *Proof*: Apply `ih` to $S = N^+(v)$ ($|S| < n$) and compare with `hdeg w`; uses zero forbidden patterns. $\square$
- **Claim 3 (`sharp_claim3` — Eliminating $O_5^{(b)}$ via Unified Witness $b$)**: If $u \to v$ and $v \to w$ are critical, then $u \perp w$. *Proof*: Assume $u \to w$. Since $w \in N^+(u) \cap N^+(v)$, the helper on $(u, v, w)$ produces **$b \in (N^+(u) \cap N^+(w)) \setminus (N^+(u) \cap N^+(v))$ with $v \perp b$**. Claim 2 on $u \to v$ gives $x$ with $v \to x, u \perp x$.
  - If $x \to w$: Claim 1 on $(u, v, w, x)$ contradicts $\neg P_1$.
  - If $w \perp x$: $\{u, v, w, x, b\} \in P_2$, contradiction!
  - Thus $w \to x$. Now apply the helper to critical $(v, w, x)$ to get $z \in (N^+(v) \cap N^+(x)) \setminus (N^+(v) \cap N^+(w))$ with $w \perp z$. By $\vec{C}_3$-freeness ($u \to v \to z$) and Claim 1 on $(u, v, z, x)$, we get $u \perp z$. Pairing $z$ with the **same** witness $b$ gives $\{u, v, w, z, b\} \in P_2$, contradiction! $\square$
- **Claim 4 (`sharp_claim4` — Eliminating 4-Vertex `TC` via `ih` on $X$)**: If $u \to v, v \to w$ are critical with $u \perp w$, then $X := N^+(u) \cap N^+(w) = \emptyset$. *Proof*: Suppose $X \ne \emptyset$. Since $u \notin X$, $|X| < n$, so `ih` on $X$ yields $x \in X$ with $3 |X \cap N^+(x)| \le |X| - 1 < n \le 3 d^+(x)$. Thus there exists $y \in N^+(x) \setminus X$ ($\neg(u \to y \land w \to y)$). By $\vec{C}_3$-freeness ($v \to w \to x$) and Claim 1 on $(u, v, x, w)$, $v \perp x$ (and $v \ne y$). Claim 1 on $(v, w, y, x)$ gives $\neg(v \to y \land w \to y)$. Hence $\{u, v, w, x, y\} \in P_4$, contradiction! $\square$
- **Claim 5 (`sharp_claim5` — Eliminating 4-Vertex `OP` via Split on $v \to x$)**: For critical $u \to v, v \to w$ with $u \perp w$, setting $U := N^+(u) \cap N^-(w)$ ($v \in U$, $u \notin U$), we have $3\,o(u, v) + 1 \le |U|$. *Proof*: `ih` on $U$ gives $v^* \in U$ with $3 |U \cap N^+(v^*)| \le |U| - 1$. We show $N^+(u) \cap N^+(v^*) \subseteq U \cap N^+(v^*)$: take $x \in N^+(u) \cap N^+(v^*)$ and suppose $\neg(x \to w)$; Claim 4 gives $x \perp w$. If $v \to x$ (covering $v^* = v$), the helper on $(u, v, x)$ produces $z$ with $v \perp z$, and $\{u, v, x, w, z\} \in P_2$! If $\neg(v \to x)$, then $v \ne v^*$ and $\{u, v, v^*, w, x\} \in P_3$! $\square$
- **Claim 6 & Telescoping (`sharp_claim6`)**: Setting $\varphi(a, b) = o(a, b) + |\{x \ne a : x \to b \land \neg(a \to x)\}|$, indicator summation + Claim 4 (giving $f(x) \le 1$ for $x \notin \{u, v, w\}$) + Claim 5 yield
  $$d^+(u) + d^+(v) + d^+(w) + \varphi(u, v) - \varphi(v, w) \le n - 1.$$
  Since every vertex has a critical out-neighbor (`hdeg`), pigeonhole yields a critical directed cycle $v_0 \to v_1 \to \cdots \to v_{\ell - 1} \to v_0$ ($\ell \ge 1$). Summing Claim 6 along the cycle cancels $\sum (\varphi(v_k, v_{k+1}) - \varphi(v_{k+1}, v_{k+2})) = 0$, giving $3 \sum_{k=0}^{\ell-1} d^+(v_k) \le \ell(n - 1)$, contradicting $3 d^+(v_k) \ge n$! $\blacksquare$

### 5.3 Critical-arc obstructions

Each example avoids the other three patterns and violates the indicated step of the critical-arc argument. [Formal witnesses](lean/CaccettaHaggkvist/RazborovSharp.lean)
- `obstructionP1_sharp` (`Fin 6`, 10 arcs): `{TC, OP, P₂, P₃, P₄}`-free, breaks **Claim 1** on critical `0 → 5`.
- `obstructionP2_sharp` (`Fin 6`, 9 arcs): `{TC, IP, P₁, P₃, P₄}`-free, breaks **Claim 3** (`5 → 4 → 1, 5 → 1`) and **Claim 5** (`4 > 1`).
- `obstructionP3_sharp` (`Fin 8`, 17 arcs, $\vec{C}_4$ on `{4,5,6,7}`): `{TC, IP, P₁, P₂, P₄}`-free, breaks **Claim 5** on critical `0 → 1 → 3` (`4 > 2`).
- `obstructionP4_sharp` (`Fin 6`, 7 arcs, $\vec{C}_4(5,1,4,0) + \{2\to 4, 2\to 5, 3\to 5\}$, **$\delta^+ = 1$ sink-free**): `{OP, IP, P₁, P₂, P₃}`-free, breaks **Claim 4** (`4 ∈ N⁺(2) ∩ N⁺(1)`) and **Claim 6** (`6 > 5`).

---

## 6. Rainbow triangles from a directed-triangle bound

The Lean reduction takes an out-degree bound as an explicit parameter. [RainbowTriangle.lean](lean/CaccettaHaggkvist/RainbowTriangle.lean)

### 6.1 Counting happy triples

A happy triple consists of three vertices spanning at least two edges. Hompe, Qu and Spirkl bound their number for graphs with $k$ edges and maximum degree at most $l$, for $l\ge k/2$. The rainbow reduction uses $l=\lfloor929k/1000\rfloor$. At this value the following counting argument suffices. [Published article](https://doi.org/10.1016/j.disc.2023.113691)

> **Lemma.** *Let $E$ be a $k$-edge simple graph ($k \ge 1$) with $\Delta(E) \le l := \lfloor \frac{929}{1000} k \rfloor$. Then the number of unordered happy triples is at most $\binom{l}{2} + \binom{k - l + 1}{2}$ (equivalently, `ordHappyTriples E ≤ 3 * (l*(l-1) + (k-l+1)*(k-l))`).*
>
> *Proof.*
> - **Case A ($\exists v, d(v) \ge k/2$)**: Every happy triple has either 2 edges at $v$ ($\binom{d}{2}$), 1 edge at $v$ and 1 outside ($\le k - d$), or 2 edges outside ($\le \binom{k - d}{2}$), totaling $\le \binom{d}{2} + \binom{k - d + 1}{2} \le \binom{l}{2} + \binom{k - l + 1}{2}$ by convexity on $[\lceil k/2 \rceil, l]$.
> - **Case B ($\Delta(E) \le D := \lfloor (k - 1)/2 \rfloor$)**: Every happy triple contains a 2-edge cherry, so `#happy ≤ \sum_x \binom{d_x}{2}`. For $k \le 14$, $\sum_x \binom{d_x}{2} \le k(D - 1) \le \binom{l}{2} + \binom{k - l + 1}{2}$ directly. For $k \ge 15$, let $s = \lfloor k/3 \rfloor$ and $H = \{x : d_x > s\}$. Writing $h=|H|$, simplicity gives $h(s+1) \le S_H := \sum_{x \in H} d_x \le k + \binom{h}{2}$ and $h(s+1) \le 2k \implies h \le 5$; if $h = 5$ then $5(\frac{k-2}{3} + 1) \le k + 10 \implies k \le 12$, contradiction! Hence $h \le 4$, so $S_H \le k + 6$, giving
>   $$\sum_x d_x(d_x - 1) \le (D - 1)(k + 6) + (s - 1)(k - 6) \le l(l - 1) + (k - l + 1)(k - l)$$
>   directly on $15 \le k \le 21$ and by one quadratic `nlinarith` step for all $k \ge 22$. $\blacksquare$

### 6.2 Reduction to Caccetta–Häggkvist & Exact Rational Parameters (`rainbow_triangle_of_ch_bound`)

Let $G$ be a rainbow-triangle-free edge-colored graph on $n \ge 1$ vertices with $n$ colors trimmed to exact size $k = \lceil t n \rceil$ each, union $E$ of size $n k$ ($2 k \le n - 1$).
- **Small-$k$ case ($k \le 2$)**: Since $t \ge \frac{79}{200}$, $k = 1$ contradicts $n \ge 3$, and $k = 2$ forces $n = 5$ ($E = K_5$), where Goodman's triangle bound gives `ordTriangles E ≥ 60` while `∑ ordHappyTriples ≤ 5 · 6 = 30`, immediate contradiction!
- **Step 1 (`rainbow_claim_conc_gt`)**: For $k \ge 3$, Goodman's 1959 bound (`goodman_ordTriangles`) plus our Zero-DP Happy-Triple Lemma implies strictly more than $(1 - \delta) n$ colors are **concentrated** ($\exists v_c, d_{E_c}(v_c) \ge \frac{929}{1000} k$) whenever $(1 - \delta(2\varepsilon - 2\varepsilon^2)) t < \frac{8}{3}(t - \frac{1}{4})$ ($\varepsilon = \frac{71}{1000}$).
- **Step 2A (Shared Center, `rainbow_case_shared_center`)**: Two distinct concentrated colors sharing a center $v$ have disjoint neighborhoods $S_1, S_2$ whose cross-edges can only use edges of $E_{c_1} \cup E_{c_2}$ not incident to $v$ (else rainbow triangle!), forcing too many non-edges of $E$ when $\frac{1}{2} - (1 - \varepsilon)^2 t^2 < t$.
- **Step 2B (Injective Centers, `rainbow_case_inj_center`)**: Distinct centers form a set $T \subseteq V$ of size $|T| > (1 - \delta) n$. Orienting $u \to w$ in $T$ whenever $u w \in E_{c(u)}$ defines a **$\vec{C}_3$-free oriented graph $D$ on $T$** (a digon would assign two colors to the same edge, and a directed triangle would give a rainbow triangle) with $\delta^+(D) \ge \frac{929}{1000} t n - (n - |T|) \ge c_{\mathrm{CH}} |T|$ whenever $c_{\mathrm{CH}}(1 - \delta) \le \frac{929}{1000} t - \delta$, contradicting the CH upper bound!

Using $c_{\rm CH}=427/1250$, $t=12457/31250$ and $\delta=2181/50000$, all three parameter inequalities hold by exact rational arithmetic. The five-vertex theorem supplies the CH hypothesis. Using $c_{\rm CH}=3383/10000$ gives $t=79697/200000$ with $\delta=4817/100000$ under the corresponding CH hypothesis. [Unconditional specialization](lean/CaccettaHaggkvist/RainbowBounds.lean) · [Six-vertex conditional specialization](lean/CaccettaHaggkvist/RainbowTriangle.lean)

## 7. Lean axiom audit

After building the default target, run `lake env lean Audit.lean` from `lean/`. The audit resolves the named public declarations and checks their transitive axiom dependencies against `propext`, `Classical.choice` and `Quot.sound`. Explicit hypotheses in a theorem's type are visible in the declaration. [Audit source](lean/Audit.lean)
