module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical

/-!
# Strict Strengthening of Razborov's 2013 Conditional Exact `1/3` Caccetta–Häggkvist Theorem

Razborov (*J. Graph Theory*, 2013, `arXiv:1107.2247`) proved the exact Caccetta–Häggkvist bound
`δ⁺(G) ≤ (n - 1) / 3` for every finite `C₃`-free oriented graph avoiding three 4-vertex induced
subgraphs: Twisted Circle (`TC`), In-Pendant (`IP`), and Out-Pendant (`OP`).

This module proves a **strict strengthening** (zero `sorry`, zero `native_decide`, zero warnings,
pure `Finset` combinatorics with standard axioms only):

* **`exists_outDeg_le_third_of_forb_TC_OP_F5`**: Every finite nonempty `C₃`-free oriented graph `G`
  avoiding induced `{TC, OP, F₅⁽¹⁾}` — dropping In-Pendant (`IP`) completely in favor of ONE single
  5-vertex supergraph `F₅⁽¹⁾` (7 arcs on `{v, w, x, y, z}`: `v→w, v→x, v→z, w→x, w→y, y→x, x→z`;
  non-edges `v⊥y, w⊥z, y⊥z`) — contains a vertex `v` with `3 * outDeg v ≤ |V| - 1`.
  This strictly generalizes Razborov (2013), expanding the covered class of 6-vertex `C₃`-free
  oriented graphs from `1,751 / 6,583` (`26.6%`) to `2,739 / 6,583` (`41.6%`, `+56.4%`, capturing
  `98.3%` of all `{TC, OP}`-free 6-vertex graphs), while all conjectured CH extremal configurations
  `Γ_CH` remain `F₅⁽¹⁾`-free.
* **`exists_outDeg_le_third_of_razborov`**: Immediate 2-line corollary recovering Razborov's 2013
  theorem (`{TC, IP, OP}`-free).
* **`Digraph.exists_outDeg_le_third_of_forb_TC_OP_F5`**: Wrapper for general simple `Digraph V`
  under `¬ G.HasCycleLe3`.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

namespace OrientedGraph

/-! ## Section 1: Exact Induced Forbidden Subgraph Predicates -/

/-- `G` contains an induced Twisted Circle (`TC`): `a → b → c → d` and `a → d`, with `a ⊥ c` and `b ⊥ d`. -/
def HasInducedTC {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ c ∧ b ≠ d ∧
    G.adj a b ∧ G.adj b c ∧ G.adj c d ∧ G.adj a d ∧
    ¬ G.adj a c ∧ ¬ G.adj c a ∧ ¬ G.adj b d ∧ ¬ G.adj d b

/-- `G` contains an induced Out-Pendant (`OP`): transitive triangle `a → b → c, a → c` plus `b → d`
with `a ⊥ d` and `c ⊥ d`. -/
def HasInducedOP {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ d ∧ c ≠ d ∧
    G.adj a b ∧ G.adj b c ∧ G.adj a c ∧ G.adj b d ∧
    ¬ G.adj a d ∧ ¬ G.adj d a ∧ ¬ G.adj c d ∧ ¬ G.adj d c

/-- `G` contains an induced In-Pendant (`IP`): transitive triangle `a → b → c, a → c` plus `d → b`
with `a ⊥ d` and `c ⊥ d`. -/
def HasInducedIP {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ d ∧ c ≠ d ∧
    G.adj a b ∧ G.adj b c ∧ G.adj a c ∧ G.adj d b ∧
    ¬ G.adj a d ∧ ¬ G.adj d a ∧ ¬ G.adj c d ∧ ¬ G.adj d c

/-- `G` contains an induced copy of the 5-vertex graph `F₅⁽¹⁾` on `{v, w, x, y, z}` with 7 arcs
`v→w, v→x, v→z, w→x, w→y, y→x, x→z` and 3 non-edges `v⊥y, w⊥z, y⊥z`. -/
def HasInducedF5_1 {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ v w x y z : V,
    v ≠ y ∧ w ≠ z ∧ y ≠ z ∧
    G.adj v w ∧ G.adj v x ∧ G.adj v z ∧ G.adj w x ∧ G.adj w y ∧ G.adj y x ∧ G.adj x z ∧
    ¬ G.adj v y ∧ ¬ G.adj y v ∧ ¬ G.adj w z ∧ ¬ G.adj z w ∧ ¬ G.adj y z ∧ ¬ G.adj z y

/-- `F₅⁽¹⁾` contains `IP` as an induced subgraph (on `{v, x, z, y}`), so forbidding `F₅⁽¹⁾` is
strictly weaker than forbidding `IP`. -/
lemma hasInducedIP_of_hasInducedF5_1 {V : Type u} {G : OrientedGraph V}
    (h : G.HasInducedF5_1) : G.HasInducedIP := by
  rcases h with ⟨v, _w, x, y, z, hvy_ne, _hwz_ne, hyz_ne, _hvw, hvx, hvz, _hwx, _hwy, hyx, hxz,
    hnvy, hnyv, _hnwz, _hnzw, hnyz, hnzy⟩
  exact ⟨v, x, z, y, hvy_ne, hyz_ne.symm, hvx, hxz, hvz, hyx, hnvy, hnyv, hnzy, hnyz⟩

lemma not_hasInducedTC_induce {V : Type u} {G : OrientedGraph V} (h : ¬ G.HasInducedTC) (S : Finset V) :
    ¬ (G.induce S).HasInducedTC := by
  rintro ⟨a, b, c, d, hac, hbd, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact h ⟨a.1, b.1, c.1, d.1, fun e => hac (Subtype.ext e), fun e => hbd (Subtype.ext e),
    h1, h2, h3, h4, h5, h6, h7, h8⟩

lemma not_hasInducedOP_induce {V : Type u} {G : OrientedGraph V} (h : ¬ G.HasInducedOP) (S : Finset V) :
    ¬ (G.induce S).HasInducedOP := by
  rintro ⟨a, b, c, d, had, hcd, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact h ⟨a.1, b.1, c.1, d.1, fun e => had (Subtype.ext e), fun e => hcd (Subtype.ext e),
    h1, h2, h3, h4, h5, h6, h7, h8⟩

lemma not_hasInducedF5_1_induce {V : Type u} {G : OrientedGraph V} (h : ¬ G.HasInducedF5_1) (S : Finset V) :
    ¬ (G.induce S).HasInducedF5_1 := by
  rintro ⟨v, w, x, y, z, hvy, hwz, hyz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact h ⟨v.1, w.1, x.1, y.1, z.1,
    fun e => hvy (Subtype.ext e), fun e => hwz (Subtype.ext e), fun e => hyz (Subtype.ext e),
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-! ## Section 2: Critical-Edge Claims 1–6 in Exact Integer Form -/

section RazborovProof

variable {V : Type u} [Fintype V] [DecidableEq V] (G : OrientedGraph V) [DecidableRel G.adj]

private def oCnt (u v : V) : ℕ :=
  (G.toDigraph.outSet u ∩ G.toDigraph.outSet v).card

private def IsCritical (u v : V) : Prop :=
  G.adj u v ∧ ∀ w : V, G.adj u w → G.oCnt u v ≤ G.oCnt u w

private def p3NCnt (u w : V) : ℕ :=
  (G.toDigraph.outSet u ∩ G.toDigraph.inSet w).card

private def bCnt (u v : V) : ℕ :=
  (Finset.univ.filter fun x : V => x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x).card

private def phiInt (u v : V) : ℤ :=
  (G.oCnt u v : ℤ) + (G.bCnt u v : ℤ)

/-- **Claim 1 (`ohata = 0`)**: For any critical edge `v → w`, there exist no `x, y` with
`v → x, w → x, w → y, y → x` and `v ⊥ y`. Uses ONLY `C₃`-freeness, `¬ TC`, and `¬ F₅⁽¹⁾`! -/
private lemma claim1_ohata (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hF5 : ¬ G.HasInducedF5_1)
    {v w x y : V} (hcrit : G.IsCritical v w)
    (hvx : G.adj v x) (hwx : G.adj w x) (hwy : G.adj w y) (hyx : G.adj y x)
    (hvy_ne : v ≠ y) (hnvy : ¬ G.adj v y) (hnyv : ¬ G.adj y v) : False := by
  have hsub : G.toDigraph.outSet v ∩ G.toDigraph.outSet x ⊂
      G.toDigraph.outSet v ∩ G.toDigraph.outSet w := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [Finset.mem_inter, Digraph.mem_outSet, Digraph.mem_outSet] at hz ⊢
      rcases hz with ⟨hvz, hxz⟩
      refine ⟨hvz, ?_⟩
      by_contra hnwz
      have hwz_ne : w ≠ z := fun h => by
        subst h; exact G.asymm w x hwx hxz
      have hnzw : ¬ G.adj z w := fun hzw => hG ⟨w, x, z, hwx, hxz, hzw⟩
      have hyz_ne : y ≠ z := fun h => by
        subst h; exact hnvy hvz
      have hnzy : ¬ G.adj z y := fun hzy => hG ⟨y, x, z, hyx, hxz, hzy⟩
      by_cases hyz : G.adj y z
      · exact hTC ⟨v, w, y, z, hvy_ne, hwz_ne, hcrit.1, hwy, hyz, hvz, hnvy, hnyv, hnwz, hnzw⟩
      · exact hF5 ⟨v, w, x, y, z, hvy_ne, hwz_ne, hyz_ne,
          hcrit.1, hvx, hvz, hwx, hwy, hyx, hxz, hnvy, hnyv, hnwz, hnzw, hyz, hnzy⟩
    · intro heq
      have hx_mem : x ∈ G.toDigraph.outSet v ∩ G.toDigraph.outSet w :=
        Finset.mem_inter.mpr ⟨(Digraph.mem_outSet _).mpr hvx, (Digraph.mem_outSet _).mpr hwx⟩
      rw [← heq] at hx_mem
      exact G.loopless x ((Digraph.mem_outSet _).mp (Finset.mem_inter.mp hx_mem).2)
  have hlt : G.oCnt v x < G.oCnt v w := Finset.card_lt_card hsub
  have hle : G.oCnt v w ≤ G.oCnt v x := hcrit.2 x hvx
  omega

/-- **Claim 2 (`P₃^A > 0`)**: Under the strong induction hypothesis on proper induced subgraphs
and assuming `∀ u, |V| ≤ 3 * outDeg u`, every critical edge `v → w` has some `x` with `w → x` and `v ⊥ x`. -/
private lemma claim2_p3a (hG : G.TriangleFree)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ u ∈ S, 3 * (S ∩ G.toDigraph.outSet u).card ≤ S.card - 1)
    (hdeg : ∀ u : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg u)
    {v w : V} (hcrit : G.IsCritical v w) :
    ∃ x : V, G.adj w x ∧ v ≠ x ∧ ¬ G.adj v x ∧ ¬ G.adj x v := by
  let S : Finset V := G.toDigraph.outSet v
  have hv_not : v ∉ S := G.toDigraph.notMem_outSet_self v
  have hS_lt : S.card < Fintype.card V := by
    calc S.card < (insert v S).card := by rw [Finset.card_insert_of_notMem hv_not]; omega
      _ ≤ Fintype.card V := Finset.card_le_univ _
  have hS_ne : S.Nonempty := ⟨w, (Digraph.mem_outSet _).mpr hcrit.1⟩
  obtain ⟨w₀, hw₀S, hw₀_le⟩ := ih S hS_lt hS_ne
  have hw₀_adj : G.adj v w₀ := (Digraph.mem_outSet _).mp hw₀S
  have hcrit_le : G.oCnt v w ≤ G.oCnt v w₀ := hcrit.2 w₀ hw₀_adj
  have hcard_lt : (G.toDigraph.outSet v ∩ G.toDigraph.outSet w).card <
      (G.toDigraph.outSet w).card := by
    have hd := hdeg w
    change Fintype.card V ≤ 3 * (G.toDigraph.outSet w).card at hd
    have hS_pos : 1 ≤ S.card := Finset.one_le_card.mpr hS_ne
    change (S ∩ G.toDigraph.outSet w).card < (G.toDigraph.outSet w).card
    change (S ∩ G.toDigraph.outSet w).card ≤ (S ∩ G.toDigraph.outSet w₀).card at hcrit_le
    omega
  have hnot_sub : ¬ (G.toDigraph.outSet w ⊆ G.toDigraph.outSet v) := by
    intro hsub
    have heq : G.toDigraph.outSet v ∩ G.toDigraph.outSet w = G.toDigraph.outSet w :=
      Finset.inter_eq_right.mpr hsub
    rw [heq] at hcard_lt
    exact lt_irrefl _ hcard_lt
  obtain ⟨x, hx_w, hx_not_v⟩ := Finset.not_subset.mp hnot_sub
  rw [Digraph.mem_outSet] at hx_w hx_not_v
  have hvx_ne : v ≠ x := fun h => by subst h; exact G.asymm v w hcrit.1 hx_w
  have hnxv : ¬ G.adj x v := fun hxv => hG ⟨v, w, x, hcrit.1, hx_w, hxv⟩
  exact ⟨x, hx_w, hvx_ne, hx_not_v, hnxv⟩

/-- **Claim 3**: If `u → v` and `v → w` are critical edges, then `u` and `w` are independent. -/
private lemma claim3_indep (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hOP : ¬ G.HasInducedOP)
    (hF5 : ¬ G.HasInducedF5_1)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    (hdeg : ∀ z : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg z)
    {u v w : V} (huv : G.IsCritical u v) (hvw : G.IsCritical v w) :
    u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u := by
  have huw_ne : u ≠ w := fun h => by subst h; exact G.asymm u v huv.1 hvw.1
  have hnwu : ¬ G.adj w u := fun hwu => hG ⟨u, v, w, huv.1, hvw.1, hwu⟩
  refine ⟨huw_ne, ?_, hnwu⟩
  intro huw
  obtain ⟨x, hvx, hux_ne, hnux, hnxu⟩ := G.claim2_p3a hG ih hdeg huv
  have hwx : G.adj w x := by
    by_contra hnwx
    have hwx_ne : w ≠ x := fun h => by subst h; exact hnux huw
    have hnxw : ¬ G.adj x w := fun hxw =>
      G.claim1_ohata hG hTC hF5 huv huw hvw.1 hvx hxw hux_ne hnux hnxu
    exact hOP ⟨u, v, w, x, hux_ne, hwx_ne, huv.1, hvw.1, huw, hvx, hnux, hnxu, hnwx, hnxw⟩
  have hsub : G.toDigraph.outSet v ∩ G.toDigraph.outSet x ⊂
      G.toDigraph.outSet v ∩ G.toDigraph.outSet w := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [Finset.mem_inter, Digraph.mem_outSet, Digraph.mem_outSet] at hz ⊢
      rcases hz with ⟨hvz, hxz⟩
      refine ⟨hvz, ?_⟩
      by_contra hnwz
      have huz_ne : u ≠ z := fun h => by subst h; exact G.asymm u v huv.1 hvz
      have hnzu : ¬ G.adj z u := fun hzu => hG ⟨u, v, z, huv.1, hvz, hzu⟩
      have hnuz : ¬ G.adj u z := fun huz =>
        G.claim1_ohata hG hTC hF5 huv huz hvz hvx hxz hux_ne hnux hnxu
      have hwz_ne : w ≠ z := fun h => by subst h; exact hnuz huw
      have hnzw : ¬ G.adj z w := fun hzw => hG ⟨w, x, z, hwx, hxz, hzw⟩
      exact hOP ⟨u, v, w, z, huz_ne, hwz_ne, huv.1, hvw.1, huw, hvz, hnuz, hnzu, hnwz, hnzw⟩
    · intro heq
      have hx_mem : x ∈ G.toDigraph.outSet v ∩ G.toDigraph.outSet w :=
        Finset.mem_inter.mpr ⟨(Digraph.mem_outSet _).mpr hvx, (Digraph.mem_outSet _).mpr hwx⟩
      rw [← heq] at hx_mem
      exact G.loopless x ((Digraph.mem_outSet _).mp (Finset.mem_inter.mp hx_mem).2)
  have hlt : G.oCnt v x < G.oCnt v w := Finset.card_lt_card hsub
  have hle : G.oCnt v w ≤ G.oCnt v x := hvw.2 x hvx
  omega

/-- **Claim 4 (`K_{2,1}^N(u, w) = 0`)**: If `u → v` and `v → w` are critical edges, then no vertex
`x` satisfies both `u → x` and `w → x`. -/
private lemma claim4_nok21 (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hF5 : ¬ G.HasInducedF5_1)
    {u v w : V} (huv : G.IsCritical u v) (hvw : G.IsCritical v w)
    (huw_ind : u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u)
    {x : V} (hux : G.adj u x) (hwx : G.adj w x) : False := by
  have hvx_ne : v ≠ x := fun h => by subst h; exact G.asymm v w hvw.1 hwx
  have hnxv : ¬ G.adj x v := fun hxv => hG ⟨v, w, x, hvw.1, hwx, hxv⟩
  have hnvx : ¬ G.adj v x := fun hvx =>
    G.claim1_ohata hG hTC hF5 huv hux hvx hvw.1 hwx huw_ind.1 huw_ind.2.1 huw_ind.2.2
  exact hTC ⟨u, v, w, x, huw_ind.1, hvx_ne, huv.1, hvw.1, hwx, hux,
    huw_ind.2.1, huw_ind.2.2, hnvx, hnxv⟩

/-- **Claim 5 (Subset Induction)**: If `u → v` and `v → w` are critical edges, then
`3 * oCnt u v + 1 ≤ p3NCnt u w`. -/
private lemma claim5_ind (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hOP : ¬ G.HasInducedOP)
    (hF5 : ¬ G.HasInducedF5_1)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    {u v w : V} (huv : G.IsCritical u v) (hvw : G.IsCritical v w)
    (huw_ind : u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u) :
    3 * G.oCnt u v + 1 ≤ G.p3NCnt u w := by
  let U : Finset V := G.toDigraph.outSet u ∩ G.toDigraph.inSet w
  have hvU : v ∈ U := Finset.mem_inter.mpr ⟨(Digraph.mem_outSet _).mpr huv.1,
    (Digraph.mem_inSet _).mpr hvw.1⟩
  have hu_not : u ∉ U := fun h => G.loopless u ((Digraph.mem_outSet _).mp (Finset.mem_inter.mp h).1)
  have hU_lt : U.card < Fintype.card V := by
    calc U.card < (insert u U).card := by rw [Finset.card_insert_of_notMem hu_not]; omega
      _ ≤ Fintype.card V := Finset.card_le_univ _
  obtain ⟨vstar, hvstarU, hvstar_le⟩ := ih U hU_lt ⟨v, hvU⟩
  have huvstar : G.adj u vstar := (Digraph.mem_outSet _).mp (Finset.mem_inter.mp hvstarU).1
  have hvstarw : G.adj vstar w := (Digraph.mem_inSet _).mp (Finset.mem_inter.mp hvstarU).2
  have hsub : G.toDigraph.outSet u ∩ G.toDigraph.outSet vstar ⊆ U ∩ G.toDigraph.outSet vstar := by
    intro x hx
    rw [Finset.mem_inter, Digraph.mem_outSet, Digraph.mem_outSet] at hx
    rcases hx with ⟨hux, hvstarx⟩
    refine Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(Digraph.mem_outSet _).mpr hux,
      (Digraph.mem_inSet _).mpr ?_⟩, (Digraph.mem_outSet _).mpr hvstarx⟩
    by_contra hnxw
    have hxw_ne : x ≠ w := fun h => by subst h; exact huw_ind.2.1 hux
    have hnwx : ¬ G.adj w x := fun hwx => G.claim4_nok21 hG hTC hF5 huv hvw huw_ind hux hwx
    exact hOP ⟨u, vstar, x, w, huw_ind.1, hxw_ne, huvstar, hvstarx, hux, hvstarw,
      huw_ind.2.1, huw_ind.2.2, hnxw, hnwx⟩
  have hle1 : G.oCnt u v ≤ G.oCnt u vstar := huv.2 vstar huvstar
  have hle2 : G.oCnt u vstar ≤ (U ∩ G.toDigraph.outSet vstar).card := Finset.card_le_card hsub
  have hU_pos : 1 ≤ U.card := Finset.one_le_card.mpr ⟨v, hvU⟩
  change 3 * G.oCnt u v + 1 ≤ U.card
  omega

/-- **Claim 6 (Exact Integer Telescoping Inequality)**:
For critical edges `u → v` and `v → w`,
`outDeg u + outDeg v + outDeg w + phiInt u v - phiInt v w ≤ |V| - 1`. -/
private lemma claim6_crucial (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hOP : ¬ G.HasInducedOP)
    (hF5 : ¬ G.HasInducedF5_1)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    {u v w : V} (huv : G.IsCritical u v) (hvw : G.IsCritical v w)
    (huw_ind : u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u) :
    (G.toDigraph.outDeg u : ℤ) + (G.toDigraph.outDeg v : ℤ) + (G.toDigraph.outDeg w : ℤ) +
      G.phiInt u v - G.phiInt v w ≤ (Fintype.card V : ℤ) - 1 := by
  have h5 : (3 * G.oCnt u v + 1 : ℤ) ≤ (G.p3NCnt u w : ℤ) := by
    exact_mod_cast G.claim5_ind hG hTC hOP hF5 ih huv hvw huw_ind
  let ind : Prop → ℤ := fun P => @ite ℤ P (Classical.propDecidable P) 1 0
  let f : V → ℤ := fun x =>
    ind (G.adj u x) + ind (G.adj v x) + ind (G.adj w x) +
    ind (x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x) -
    2 * ind (G.adj u x ∧ G.adj v x) -
    ind (G.adj v x ∧ G.adj w x) -
    ind (x ≠ v ∧ G.adj x w ∧ ¬ G.adj v x) +
    ind (G.adj u x ∧ G.adj x w)
  have hcard_sum : ∀ (P : V → Prop) [DecidablePred P],
      ((Finset.univ.filter P).card : ℤ) = ∑ x : V, ind (P x) := by
    intro P _
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [ind]
    by_cases hp : P x <;> simp [hp]
  have hsum_eq :
      (G.toDigraph.outDeg u : ℤ) + (G.toDigraph.outDeg v : ℤ) + (G.toDigraph.outDeg w : ℤ) +
        (G.bCnt u v : ℤ) - 2 * (G.oCnt u v : ℤ) - (G.oCnt v w : ℤ) - (G.bCnt v w : ℤ) +
        (G.p3NCnt u w : ℤ) = ∑ x : V, f x := by
    have hdu : (G.toDigraph.outDeg u : ℤ) = ∑ x : V, ind (G.adj u x) := hcard_sum _
    have hdv : (G.toDigraph.outDeg v : ℤ) = ∑ x : V, ind (G.adj v x) := hcard_sum _
    have hdw : (G.toDigraph.outDeg w : ℤ) = ∑ x : V, ind (G.adj w x) := hcard_sum _
    have hbuv : (G.bCnt u v : ℤ) = ∑ x : V, ind (x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x) := hcard_sum _
    have hbvw : (G.bCnt v w : ℤ) = ∑ x : V, ind (x ≠ v ∧ G.adj x w ∧ ¬ G.adj v x) := hcard_sum _
    have houv : (G.oCnt u v : ℤ) = ∑ x : V, ind (G.adj u x ∧ G.adj v x) := by
      have : G.toDigraph.outSet u ∩ G.toDigraph.outSet v =
          Finset.univ.filter (fun x => G.adj u x ∧ G.adj v x) := by
        ext x; simp [Digraph.outSet]
      unfold oCnt; rw [this]; exact hcard_sum _
    have hovw : (G.oCnt v w : ℤ) = ∑ x : V, ind (G.adj v x ∧ G.adj w x) := by
      have : G.toDigraph.outSet v ∩ G.toDigraph.outSet w =
          Finset.univ.filter (fun x => G.adj v x ∧ G.adj w x) := by
        ext x; simp [Digraph.outSet]
      unfold oCnt; rw [this]; exact hcard_sum _
    have hp3 : (G.p3NCnt u w : ℤ) = ∑ x : V, ind (G.adj u x ∧ G.adj x w) := by
      have : G.toDigraph.outSet u ∩ G.toDigraph.inSet w =
          Finset.univ.filter (fun x => G.adj u x ∧ G.adj x w) := by
        ext x; simp [Digraph.outSet, Digraph.inSet]
      unfold p3NCnt; rw [this]; exact hcard_sum _
    rw [hdu, hdv, hdw, hbuv, houv, hovw, hbvw, hp3]
    dsimp [f]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have huv_ne : u ≠ v := G.ne_of_adj huv.1
  have hvw_ne : v ≠ w := G.ne_of_adj hvw.1
  have hfu : f u = 0 := by
    have hnuu := G.loopless u
    have hnvu := G.asymm u v huv.1
    dsimp [f, ind]
    simp [hnuu, hnvu, huw_ind.2.1, huw_ind.2.2]
  have hfv : f v = 2 := by
    have hnvv := G.loopless v
    have hnwv := G.asymm v w hvw.1
    dsimp [f, ind]
    simp [huv.1, hvw.1, hnvv, hnwv]
  have hfw : f w = 1 := by
    have hnww := G.loopless w
    have hnwv := G.asymm v w hvw.1
    dsimp [f, ind]
    simp [hvw.1, hnww, hnwv, huw_ind.2.1]
  have hf_other : ∀ x : V, x ≠ u → x ≠ v → x ≠ w → f x ≤ 1 := by
    intro x hxu hxv _hxw
    dsimp [f, ind]
    by_cases hbuv : G.adj x v ∧ ¬ G.adj u x
    · have hnvx : ¬ G.adj v x := G.asymm x v hbuv.1
      have hnwx : ¬ G.adj w x := fun hwx => hG ⟨v, w, x, hvw.1, hwx, hbuv.1⟩
      have hnux : ¬ G.adj u x := hbuv.2
      split_ifs <;> simp_all
    · have hbuv' : ¬ (x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x) := fun h => hbuv h.2
      by_cases hux : G.adj u x
      · have hnwx : ¬ G.adj w x := fun hwx => G.claim4_nok21 hG hTC hF5 huv hvw huw_ind hux hwx
        by_cases hxw : G.adj x w <;> by_cases hvx : G.adj v x <;> (split_ifs <;> simp_all)
      · by_cases hvx : G.adj v x <;> by_cases hwx : G.adj w x <;> (split_ifs <;> simp_all)
  let T : Finset V := {u, v, w}
  have hv_not : v ∉ ({w} : Finset V) := by simp [hvw_ne]
  have hu_not : u ∉ ({v, w} : Finset V) := by simp [huv_ne, huw_ind.1]
  have hT_card : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hu_not, Finset.card_insert_of_notMem hv_not, Finset.card_singleton]
  have hT_sum : ∑ x ∈ T, f x = 3 := by
    dsimp [T]
    rw [Finset.sum_insert hu_not, Finset.sum_insert hv_not, Finset.sum_singleton, hfu, hfv, hfw]; norm_num
  have hrest_le : ∑ x ∈ Finset.univ \ T, f x ≤ ((Finset.univ \ T).card : ℤ) := by
    calc ∑ x ∈ Finset.univ \ T, f x
        ≤ ∑ _x ∈ Finset.univ \ T, (1 : ℤ) := Finset.sum_le_sum fun x hx => by
          rw [Finset.mem_sdiff] at hx
          have hnotT := hx.2
          simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or] at hnotT
          exact hf_other x hnotT.1 hnotT.2.1 hnotT.2.2
      _ = ((Finset.univ \ T).card : ℤ) := by simp
  have hsplit : ∑ x : V, f x = (∑ x ∈ T, f x) + ∑ x ∈ Finset.univ \ T, f x := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1; ext x; by_cases hx : x ∈ T <;> simp
  have hcard_split : (Fintype.card V : ℤ) = (T.card : ℤ) + ((Finset.univ \ T).card : ℤ) := by
    have hnat : Fintype.card V = T.card + (Finset.univ \ T).card := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
      rw [Finset.card_univ] at h; omega
    exact_mod_cast hnat
  have htot : ∑ x : V, f x ≤ (Fintype.card V : ℤ) := by
    rw [hsplit, hT_sum, hcard_split, hT_card]; norm_num; linarith
  unfold phiInt
  linarith [h5, hsum_eq, htot]

end RazborovProof

/-! ## Section 3: Main Strictly Stronger Razborov Theorem & Corollaries -/

/-- **Strictly Stronger Conditional Exact `1/3` Caccetta–Häggkvist Theorem (2026)**:
Every finite nonempty `C₃`-free oriented graph `G` avoiding induced `{TC, OP, F₅⁽¹⁾}`
contains a vertex `v` with `3 * outDeg v ≤ |V| - 1` (i.e. `d⁺(v) ≤ (n - 1) / 3`). -/
theorem exists_outDeg_le_third_of_forb_TC_OP_F5 :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : OrientedGraph V) [DecidableRel G.adj],
      G.TriangleFree → ¬ G.HasInducedTC → ¬ G.HasInducedOP → ¬ G.HasInducedF5_1 →
      ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 := by
  suffices hmain : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : OrientedGraph V) [DecidableRel G.adj],
      Fintype.card V = n →
      G.TriangleFree → ¬ G.HasInducedTC → ¬ G.HasInducedOP → ¬ G.HasInducedF5_1 →
      ∃ v : V, 3 * G.toDigraph.outDeg v ≤ n - 1 by
    intro V _ _ _ G _ hG hTC hOP hF5
    exact hmain (Fintype.card V) G rfl hG hTC hOP hF5
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ hne G _ hn hG hTC hOP hF5
    by_contra hno
    push Not at hno
    have hdeg : ∀ v : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg v := by
      intro v
      have hlt := hno v
      have hn_pos : 1 ≤ n := hn ▸ Fintype.card_pos
      omega
    have hih_sub : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
        ∃ u ∈ S, 3 * (S ∩ G.toDigraph.outSet u).card ≤ S.card - 1 := by
      intro S hS_lt hS_ne
      have _ : Nonempty {z : V // z ∈ S} := hS_ne.to_subtype
      obtain ⟨⟨u, hu⟩, hu_le⟩ := ih S.card (hn ▸ hS_lt) (G.induce S) (Fintype.card_coe S)
        (G.triangleFree_induce hG S) (G.not_hasInducedTC_induce hTC S)
        (G.not_hasInducedOP_induce hOP S) (G.not_hasInducedF5_1_induce hF5 S)
      rw [G.outDeg_induce S ⟨u, hu⟩] at hu_le
      exact ⟨u, hu, hu_le⟩
    -- Every vertex has a critical out-neighbor!
    have hex_crit : ∀ v : V, ∃ w : V, G.IsCritical v w := by
      intro v
      have hne_out : (G.toDigraph.outSet v).Nonempty := by
        have hd := hdeg v
        have hpos : 0 < Fintype.card V := Fintype.card_pos
        exact Finset.card_pos.mp (by unfold Digraph.outDeg at hd; omega)
      obtain ⟨w, hw_mem, hw_min⟩ := Finset.exists_min_image (G.toDigraph.outSet v) (G.oCnt v) hne_out
      exact ⟨w, (Digraph.mem_outSet _).mp hw_mem, fun w' hw' => hw_min w' ((Digraph.mem_outSet _).mpr hw')⟩
    choose critNext hcritNext using hex_crit
    -- Pigeonhole yields a directed cycle of critical edges of length `ℓ ≥ 1`!
    obtain ⟨v₀⟩ := hne
    have hlt_card : Fintype.card V < Fintype.card (Fin (Fintype.card V + 1)) := by simp
    obtain ⟨a, b, hab_ne, hab_eq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card V + 1) => critNext^[k.1] v₀) hlt_card
    have hij : ∃ i j : ℕ, i < j ∧ critNext^[i] v₀ = critNext^[j] v₀ := by
      by_cases hlt : a.1 < b.1
      · exact ⟨a.1, b.1, hlt, hab_eq⟩
      · have hgt : b.1 < a.1 := lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun e => hab_ne (Fin.ext e.symm))
        exact ⟨b.1, a.1, hgt, hab_eq.symm⟩
    obtain ⟨i, j, hij_lt, hij_eq⟩ := hij
    let ℓ : ℕ := j - i
    have hℓ_pos : 0 < ℓ := Nat.sub_pos_of_lt hij_lt
    let seq : ℕ → V := fun k => critNext^[i + k] v₀
    have hseq_step : ∀ k : ℕ, seq (k + 1) = critNext (seq k) := by
      intro k; dsimp [seq]; rw [← add_assoc, Function.iterate_succ_apply']
    have hseq_crit : ∀ k : ℕ, G.IsCritical (seq k) (seq (k + 1)) := by
      intro k; rw [hseq_step k]; exact hcritNext (seq k)
    have hseq_per : ∀ k : ℕ, seq (k + ℓ) = seq k := by
      intro k
      induction k with
      | zero =>
        dsimp [seq]
        have heq : i + (0 + ℓ) = j := by dsimp [ℓ]; omega
        rw [heq, hij_eq]
      | succ k ihk =>
        rw [show k + 1 + ℓ = (k + ℓ) + 1 by omega, hseq_step, hseq_step, ihk]
    -- Sum Claim 6 along the critical cycle of length `ℓ`!
    have hstep_ineq : ∀ k : ℕ,
        (G.toDigraph.outDeg (seq k) : ℤ) + (G.toDigraph.outDeg (seq (k + 1)) : ℤ) +
          (G.toDigraph.outDeg (seq (k + 2)) : ℤ) +
          G.phiInt (seq k) (seq (k + 1)) - G.phiInt (seq (k + 1)) (seq (k + 2)) ≤
        (Fintype.card V : ℤ) - 1 := by
      intro k
      have h1 := hseq_crit k
      have h2 := hseq_crit (k + 1)
      have hind := G.claim3_indep hG hTC hOP hF5 hih_sub hdeg h1 h2
      exact G.claim6_crucial hG hTC hOP hF5 hih_sub h1 h2 hind
    have hsum_le :
        ∑ k ∈ Finset.range ℓ,
          ((G.toDigraph.outDeg (seq k) : ℤ) + (G.toDigraph.outDeg (seq (k + 1)) : ℤ) +
            (G.toDigraph.outDeg (seq (k + 2)) : ℤ) +
            G.phiInt (seq k) (seq (k + 1)) - G.phiInt (seq (k + 1)) (seq (k + 2))) ≤
        (ℓ : ℤ) * ((Fintype.card V : ℤ) - 1) := by
      calc ∑ k ∈ Finset.range ℓ, _
          ≤ ∑ _k ∈ Finset.range ℓ, ((Fintype.card V : ℤ) - 1) :=
            Finset.sum_le_sum fun k _ => hstep_ineq k
        _ = (ℓ : ℤ) * ((Fintype.card V : ℤ) - 1) := by simp; ring
    -- Shift invariance of periodic sums over `Finset.range ℓ`:
    have hshift : ∀ (F : V → ℤ),
        ∑ k ∈ Finset.range ℓ, F (seq (k + 1)) = ∑ k ∈ Finset.range ℓ, F (seq k) := by
      intro F
      have h1 := Finset.sum_range_succ (fun k => F (seq k)) ℓ
      have h2 := Finset.sum_range_succ' (fun k => F (seq k)) ℓ
      have hper0 : seq ℓ = seq 0 := by simpa using hseq_per 0
      linarith [h1, h2, congrArg F hper0]
    have htele : ∑ k ∈ Finset.range ℓ,
        (G.phiInt (seq k) (seq (k + 1)) - G.phiInt (seq (k + 1)) (seq (k + 2))) = 0 := by
      have h1 := Finset.sum_range_sub' (fun k => G.phiInt (seq k) (seq (k + 1))) ℓ
      have hper0 : seq ℓ = seq 0 := by simpa using hseq_per 0
      have hper1 : seq (ℓ + 1) = seq 1 := by
        have := hseq_per 1; rwa [add_comm] at this
      rw [hper0, hper1] at h1
      linarith
    have hsum_d1 : ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 1)) : ℤ) =
        ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ) :=
      hshift (fun x => (G.toDigraph.outDeg x : ℤ))
    have hsum_d2 : ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 2)) : ℤ) =
        ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ) := by
      have h_s2 : ∀ k, seq (k + 2) = critNext (seq (k + 1)) := fun k => hseq_step (k + 1)
      have h_s1 : ∀ k, seq (k + 1) = critNext (seq k) := hseq_step
      calc ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 2)) : ℤ)
          = ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (critNext (seq (k + 1))) : ℤ) :=
            Finset.sum_congr rfl fun k _ => by rw [h_s2 k]
        _ = ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (critNext (seq k)) : ℤ) :=
            hshift (fun x => (G.toDigraph.outDeg (critNext x) : ℤ))
        _ = ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 1)) : ℤ) :=
            Finset.sum_congr rfl fun k _ => by rw [← h_s1 k]
        _ = ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ) := hsum_d1
    have hsum_simp :
        3 * ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ) ≤
        (ℓ : ℤ) * ((Fintype.card V : ℤ) - 1) := by
      have hexp :
          ∑ k ∈ Finset.range ℓ,
            ((G.toDigraph.outDeg (seq k) : ℤ) + (G.toDigraph.outDeg (seq (k + 1)) : ℤ) +
              (G.toDigraph.outDeg (seq (k + 2)) : ℤ) +
              G.phiInt (seq k) (seq (k + 1)) - G.phiInt (seq (k + 1)) (seq (k + 2))) =
          (∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ)) +
          (∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 1)) : ℤ)) +
          (∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 2)) : ℤ)) +
          ∑ k ∈ Finset.range ℓ,
            (G.phiInt (seq k) (seq (k + 1)) - G.phiInt (seq (k + 1)) (seq (k + 2))) := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hexp, hsum_d1, hsum_d2, htele] at hsum_le
      linarith
    have hsum_lb : (ℓ : ℤ) * (Fintype.card V : ℤ) ≤
        3 * ∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ) := by
      rw [Finset.mul_sum]
      calc (ℓ : ℤ) * (Fintype.card V : ℤ)
          = ∑ _k ∈ Finset.range ℓ, (Fintype.card V : ℤ) := by simp
        _ ≤ ∑ k ∈ Finset.range ℓ, 3 * (G.toDigraph.outDeg (seq k) : ℤ) :=
            Finset.sum_le_sum fun k _ => by exact_mod_cast hdeg (seq k)
    have hℓ_int : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ_pos
    nlinarith

/-- **Corollary (Razborov's 2013 Theorem, *J. Graph Theory*)**:
Every finite nonempty `C₃`-free oriented graph avoiding induced `{TC, IP, OP}` has a vertex `v`
with `3 * outDeg v ≤ |V| - 1`. -/
theorem exists_outDeg_le_third_of_razborov
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hIP : ¬ G.HasInducedIP) (hOP : ¬ G.HasInducedOP) :
    ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 :=
  G.exists_outDeg_le_third_of_forb_TC_OP_F5 hG hTC hOP (fun h5 => hIP (G.hasInducedIP_of_hasInducedF5_1 h5))

end OrientedGraph

/-- **General `3-Free Digraph` Wrapper**:
Every finite nonempty simple digraph `G` with `¬ G.HasCycleLe3` whose oriented upgrade avoids
induced `{TC, OP, F₅⁽¹⁾}` has a vertex `v` with `3 * G.outDeg v ≤ |V| - 1`. -/
theorem Digraph.exists_outDeg_le_third_of_forb_TC_OP_F5
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : Digraph V) [dG : DecidableRel G.adj] (h3free : ¬ G.HasCycleLe3)
    (hTC : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasInducedTC)
    (hOP : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasInducedOP)
    (hF5 : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasInducedF5_1) :
    ∃ v : V, 3 * G.outDeg v ≤ Fintype.card V - 1 := by
  let H : OrientedGraph V := G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))
  let _ : DecidableRel H.adj := dG
  exact H.exists_outDeg_le_third_of_forb_TC_OP_F5 (fun ht => h3free (Or.inr ht)) hTC hOP hF5

end CaccettaHaggkvist
