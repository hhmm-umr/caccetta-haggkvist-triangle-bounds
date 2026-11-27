module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical
public import CaccettaHaggkvist.RazborovExact

/-!
# The one-third bound under four forbidden five-vertex patterns

Every nonempty directed-triangle-free oriented graph avoiding `HasPattern1` through
`HasPattern4` has a vertex with `3 * outDeg v ≤ n - 1`. The argument uses
Razborov’s critical-edge method. The final section gives four finite examples.
Each avoids the other three patterns and violates an intermediate critical-edge claim.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

namespace OrientedGraph

/-! ## Section 1: The Four Partial 5-Vertex Forbidden Patterns (ZERO 4-Vertex Graphs) -/

/-- **Pattern `P₁` (Claim 1 guard — 2 five-vertex graphs: `F₅⁽¹⁾` and `T₅⁽¹⁾`)**:
`v → w, v → x, v → z, w → x, w → y, y → x, x → z` with `v ⊥ y` and `w ⊥ z`.
Strictly relaxes `{TC, IP}` (every `C₃`-free instance contains `F₅⁽¹⁾ ⊃ IP` or `T₅⁽¹⁾ ⊃ TC`). -/
def HasPattern1 {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ v w x y z : V,
    v ≠ y ∧ w ≠ z ∧ y ≠ z ∧
    G.adj v w ∧ G.adj v x ∧ G.adj v z ∧ G.adj w x ∧ G.adj w y ∧ G.adj y x ∧ G.adj x z ∧
    ¬ G.adj v y ∧ ¬ G.adj y v ∧ ¬ G.adj w z ∧ ¬ G.adj z w

/-- **Pattern `P₂` (Claim 3 & Claim 5A guard — 3 five-vertex graphs: `O₅⁽ᵃ⁾, C3a_zx, C3a_xz`)**:
`u → v, u → w, u → z, v → w, v → x, w → z` with `u ⊥ x`, `v ⊥ z`, `w ⊥ x`, `x ≠ z`.
Every instance contains an induced `OP` on `{u, v, w, x}`. -/
def HasPattern2 {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ u v w x z : V,
    u ≠ x ∧ v ≠ z ∧ w ≠ x ∧ x ≠ z ∧
    G.adj u v ∧ G.adj u w ∧ G.adj u z ∧ G.adj v w ∧ G.adj v x ∧ G.adj w z ∧
    ¬ G.adj u x ∧ ¬ G.adj x u ∧ ¬ G.adj v z ∧ ¬ G.adj z v ∧ ¬ G.adj w x ∧ ¬ G.adj x w

/-- **Pattern `P₃` (Claim 5B guard — 5 five-vertex graphs, 1 overlapping `P₂`, so 4 new)**:
`u → v, u → v', u → x, v → w, v' → w, v' → x` with `v ≠ v'`, `u ⊥ w`, `x ⊥ w`, `¬ (v → x)`.
Every instance contains an induced `OP` on `{u, v', x, w}`. -/
def HasPattern3 {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ u v v' w x : V,
    v ≠ v' ∧ u ≠ w ∧ x ≠ w ∧
    G.adj u v ∧ G.adj u v' ∧ G.adj u x ∧ G.adj v w ∧ G.adj v' w ∧ G.adj v' x ∧
    ¬ G.adj u w ∧ ¬ G.adj w u ∧ ¬ G.adj x w ∧ ¬ G.adj w x ∧ ¬ G.adj v x

/-- **Pattern `P₄` (`TC⁺`, Claim 4 guard — 7 five-vertex graphs)**:
Induced `TC` (`u → v → w → x, u → x, u ⊥ w, v ⊥ x`) plus an outgoing arc `x → y` with
`v ≠ y`, `¬ (v → y ∧ w → y)`, and `¬ (u → y ∧ w → y)`.
Every instance contains an induced `TC` on `{u, v, w, x}`. -/
def HasPattern4 {V : Type u} (G : OrientedGraph V) : Prop :=
  ∃ u v w x y : V,
    u ≠ w ∧ v ≠ x ∧ v ≠ y ∧
    G.adj u v ∧ G.adj v w ∧ G.adj w x ∧ G.adj u x ∧ G.adj x y ∧
    ¬ G.adj u w ∧ ¬ G.adj w u ∧ ¬ G.adj v x ∧ ¬ G.adj x v ∧
    ¬ (G.adj v y ∧ G.adj w y) ∧ ¬ (G.adj u y ∧ G.adj w y)

/-! ### Strict Relaxation Lemmas (`{TC, OP, IP}` and `{TC, OP, F₅⁽¹⁾}` imply `{P₁, P₂, P₃, P₄}`-free) -/

lemma not_hasPattern1_of_not_TC_F5 {V : Type u} {G : OrientedGraph V}
    (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hF5 : ¬ G.HasInducedF5_1) :
    ¬ G.HasPattern1 := by
  rintro ⟨v, w, x, y, z, hvy_ne, hwz_ne, hyz_ne, hvw, hvx, hvz, hwx, hwy, hyx, hxz,
    hnvy, hnyv, hnwz, hnzw⟩
  have hnzy : ¬ G.adj z y := fun hzy => hG ⟨y, x, z, hyx, hxz, hzy⟩
  by_cases hyz : G.adj y z
  · exact hTC ⟨v, w, y, z, hvy_ne, hwz_ne, hvw, hwy, hyz, hvz, hnvy, hnyv, hnwz, hnzw⟩
  · exact hF5 ⟨v, w, x, y, z, hvy_ne, hwz_ne, hyz_ne, hvw, hvx, hvz, hwx, hwy, hyx, hxz,
      hnvy, hnyv, hnwz, hnzw, hyz, hnzy⟩

lemma hasInducedOP_of_hasPattern2 {V : Type u} {G : OrientedGraph V}
    (h : G.HasPattern2) : G.HasInducedOP := by
  rcases h with ⟨u, v, w, x, _z, hux_ne, _hvz_ne, hwx_ne, _hxz_ne,
    huv, huw, _huz, hvw, hvx, _hwz, hnux, hnxu, _hnvz, _hnzv, hnwx, hnxw⟩
  exact ⟨u, v, w, x, hux_ne, hwx_ne, huv, hvw, huw, hvx, hnux, hnxu, hnwx, hnxw⟩

lemma hasInducedOP_of_hasPattern3 {V : Type u} {G : OrientedGraph V}
    (h : G.HasPattern3) : G.HasInducedOP := by
  rcases h with ⟨u, _v, v', w, x, _hvv', huw_ne, hxw_ne,
    _huv, huv', hux, _hvw, hv'w, hv'x, hnuw, hnwu, hnxw, hnwx, _hnvx⟩
  exact ⟨u, v', x, w, huw_ne, hxw_ne, huv', hv'x, hux, hv'w, hnuw, hnwu, hnxw, hnwx⟩

lemma hasInducedTC_of_hasPattern4 {V : Type u} {G : OrientedGraph V}
    (h : G.HasPattern4) : G.HasInducedTC := by
  rcases h with ⟨u, v, w, x, _y, huw_ne, hvx_ne, _hvy_ne,
    huv, hvw, hwx, hux, _hxy, hnuw, hnwu, hnvx, hnxv, _, _⟩
  exact ⟨u, v, w, x, huw_ne, hvx_ne, huv, hvw, hwx, hux, hnuw, hnwu, hnvx, hnxv⟩

/-! ### Heredity Under Induced Subgraphs -/

lemma not_hasPattern1_induce {V : Type u} {G : OrientedGraph V}
    (h : ¬ G.HasPattern1) (S : Finset V) : ¬ (G.induce S).HasPattern1 := by
  rintro ⟨v, w, x, y, z, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  exact h ⟨v.1, w.1, x.1, y.1, z.1,
    fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), fun e => h3 (Subtype.ext e),
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

lemma not_hasPattern2_induce {V : Type u} {G : OrientedGraph V}
    (h : ¬ G.HasPattern2) (S : Finset V) : ¬ (G.induce S).HasPattern2 := by
  rintro ⟨u, v, w, x, z, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  exact h ⟨u.1, v.1, w.1, x.1, z.1,
    fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e),
    fun e => h3 (Subtype.ext e), fun e => h4 (Subtype.ext e),
    h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

lemma not_hasPattern3_induce {V : Type u} {G : OrientedGraph V}
    (h : ¬ G.HasPattern3) (S : Finset V) : ¬ (G.induce S).HasPattern3 := by
  rintro ⟨u, v, v', w, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  exact h ⟨u.1, v.1, v'.1, w.1, x.1,
    fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), fun e => h3 (Subtype.ext e),
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

lemma not_hasPattern4_induce {V : Type u} {G : OrientedGraph V}
    (h : ¬ G.HasPattern4) (S : Finset V) : ¬ (G.induce S).HasPattern4 := by
  rintro ⟨u, v, w, x, y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  exact h ⟨u.1, v.1, w.1, x.1, y.1,
    fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), fun e => h3 (Subtype.ext e),
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## Section 2: Critical-Edge Claims 1–6 Using ONLY `¬ P₁, ¬ P₂, ¬ P₃, ¬ P₄` -/

section SharpProof

variable {V : Type u} [Fintype V] [DecidableEq V] (G : OrientedGraph V) [DecidableRel G.adj]

/-- Number of common out-neighbors `|N⁺(u) ∩ N⁺(v)|`. -/
def critOCnt (u v : V) : ℕ :=
  (G.toDigraph.outSet u ∩ G.toDigraph.outSet v).card

/-- `u → v` is a critical arc out of `u` (minimizing `|N⁺(u) ∩ N⁺(v)|`). -/
def IsCritArc (u v : V) : Prop :=
  G.adj u v ∧ ∀ w : V, G.adj u w → G.critOCnt u v ≤ G.critOCnt u w

/-- Number of directed 2-paths `u → x → w`, i.e. `|N⁺(u) ∩ N⁻(w)|`. -/
def critP3NCnt (u w : V) : ℕ :=
  (G.toDigraph.outSet u ∩ G.toDigraph.inSet w).card

/-- Number of non-out-neighbors of `u` (other than `u`) pointing into `v`. -/
def critBCnt (u v : V) : ℕ :=
  (Finset.univ.filter fun x : V => x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x).card

/-- Integer telescoping potential `φ(u, v) = o(u, v) + b(u, v)`. -/
def critPhiInt (u v : V) : ℤ :=
  (G.critOCnt u v : ℤ) + (G.critBCnt u v : ℤ)

/-- Helper: if `a → b` is critical and `c ∈ N⁺(a) ∩ N⁺(b)`, there exists
`z ∈ (N⁺(a) ∩ N⁺(c)) \ (N⁺(a) ∩ N⁺(b))` with `b ⊥ z`. -/
private lemma exists_diff_out_of_crit (hG : G.TriangleFree) {a b c : V}
    (hab : G.IsCritArc a b) (hac : G.adj a c) (hbc : G.adj b c) :
    ∃ z : V, G.adj a z ∧ G.adj c z ∧ b ≠ z ∧ ¬ G.adj b z ∧ ¬ G.adj z b := by
  have hnot_sub : ¬ (G.toDigraph.outSet a ∩ G.toDigraph.outSet c ⊆
      G.toDigraph.outSet a ∩ G.toDigraph.outSet b) := by
    intro hsub
    have hssub : G.toDigraph.outSet a ∩ G.toDigraph.outSet c ⊂
        G.toDigraph.outSet a ∩ G.toDigraph.outSet b := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hsub, fun heq => ?_⟩
      have hc_mem : c ∈ G.toDigraph.outSet a ∩ G.toDigraph.outSet b :=
        Finset.mem_inter.mpr ⟨(Digraph.mem_outSet _).mpr hac, (Digraph.mem_outSet _).mpr hbc⟩
      rw [← heq] at hc_mem
      exact G.loopless c ((Digraph.mem_outSet _).mp (Finset.mem_inter.mp hc_mem).2)
    have hlt : G.critOCnt a c < G.critOCnt a b := Finset.card_lt_card hssub
    have hle : G.critOCnt a b ≤ G.critOCnt a c := hab.2 c hac
    omega
  obtain ⟨z, hz_ac, hz_not_ab⟩ := Finset.not_subset.mp hnot_sub
  rw [Finset.mem_inter, Digraph.mem_outSet, Digraph.mem_outSet] at hz_ac hz_not_ab
  rcases hz_ac with ⟨haz, hcz⟩
  have hnbz : ¬ G.adj b z := fun hbz => hz_not_ab ⟨haz, hbz⟩
  have hbz_ne : b ≠ z := fun h => by subst h; exact G.asymm b c hbc hcz
  have hnzb : ¬ G.adj z b := fun hzb => hG ⟨b, c, z, hbc, hcz, hzb⟩
  exact ⟨z, haz, hcz, hbz_ne, hnbz, hnzb⟩

/-- **Claim 1 (`ohata = 0`)**: Uses ONLY `C₃`-freeness and `¬ P₁` (ZERO 4-vertex graphs!). -/
private lemma sharp_claim1 (hG : G.TriangleFree) (hP1 : ¬ G.HasPattern1)
    {v w x y : V} (hcrit : G.IsCritArc v w)
    (hvx : G.adj v x) (hwx : G.adj w x) (hwy : G.adj w y) (hyx : G.adj y x)
    (hvy_ne : v ≠ y) (hnvy : ¬ G.adj v y) (hnyv : ¬ G.adj y v) : False := by
  obtain ⟨z, hvz, hxz, hwz_ne, hnwz, hnzw⟩ := G.exists_diff_out_of_crit hG hcrit hvx hwx
  have hyz_ne : y ≠ z := fun h => by subst h; exact hnvy hvz
  exact hP1 ⟨v, w, x, y, z, hvy_ne, hwz_ne, hyz_ne,
    hcrit.1, hvx, hvz, hwx, hwy, hyx, hxz, hnvy, hnyv, hnwz, hnzw⟩

/-- **Claim 2 (`P₃^A > 0`)**: Uses ONLY `C₃`-freeness, `ih`, and `hdeg` (ZERO forbidden subgraphs!). -/
private lemma sharp_claim2 (hG : G.TriangleFree)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ u ∈ S, 3 * (S ∩ G.toDigraph.outSet u).card ≤ S.card - 1)
    (hdeg : ∀ u : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg u)
    {v w : V} (hcrit : G.IsCritArc v w) :
    ∃ x : V, G.adj w x ∧ v ≠ x ∧ ¬ G.adj v x ∧ ¬ G.adj x v := by
  let S : Finset V := G.toDigraph.outSet v
  have hv_not : v ∉ S := G.toDigraph.notMem_outSet_self v
  have hS_lt : S.card < Fintype.card V := by
    calc S.card < (insert v S).card := by rw [Finset.card_insert_of_notMem hv_not]; omega
      _ ≤ Fintype.card V := Finset.card_le_univ _
  have hS_ne : S.Nonempty := ⟨w, (Digraph.mem_outSet _).mpr hcrit.1⟩
  obtain ⟨w₀, hw₀S, hw₀_le⟩ := ih S hS_lt hS_ne
  have hw₀_adj : G.adj v w₀ := (Digraph.mem_outSet _).mp hw₀S
  have hcrit_le : G.critOCnt v w ≤ G.critOCnt v w₀ := hcrit.2 w₀ hw₀_adj
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

/-- **Claim 3 (Independent critical 2-path)**: Uses ONLY `¬ P₁` and `¬ P₂`!
Key discovery: obtaining `b ∈ (N⁺(u) ∩ N⁺(w)) \ (N⁺(u) ∩ N⁺(v))` upfront closes BOTH Step 3a
and Step 3b via `P₂`, completely eliminating `O₅⁽ᵇ⁾`! -/
private lemma sharp_claim3 (hG : G.TriangleFree) (hP1 : ¬ G.HasPattern1) (hP2 : ¬ G.HasPattern2)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    (hdeg : ∀ z : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg z)
    {u v w : V} (huv : G.IsCritArc u v) (hvw : G.IsCritArc v w) :
    u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u := by
  have huw_ne : u ≠ w := fun h => by subst h; exact G.asymm u v huv.1 hvw.1
  have hnwu : ¬ G.adj w u := fun hwu => hG ⟨u, v, w, huv.1, hvw.1, hwu⟩
  refine ⟨huw_ne, ?_, hnwu⟩
  intro huw
  obtain ⟨b, hub, hwb, hvb_ne, hnvb, hnbv⟩ := G.exists_diff_out_of_crit hG huv huw hvw.1
  obtain ⟨x, hvx, hux_ne, hnux, hnxu⟩ := G.sharp_claim2 hG ih hdeg huv
  have hwx : G.adj w x := by
    by_contra hnwx
    have hwx_ne : w ≠ x := fun h => by subst h; exact hnux huw
    have hnxw : ¬ G.adj x w := fun hxw =>
      G.sharp_claim1 hG hP1 huv huw hvw.1 hvx hxw hux_ne hnux hnxu
    have hxb_ne : x ≠ b := fun h => by subst h; exact hnux hub
    exact hP2 ⟨u, v, w, x, b, hux_ne, hvb_ne, hwx_ne, hxb_ne,
      huv.1, huw, hub, hvw.1, hvx, hwb, hnux, hnxu, hnvb, hnbv, hnwx, hnxw⟩
  obtain ⟨z, hvz, hxz, hwz_ne, hnwz, hnzw⟩ := G.exists_diff_out_of_crit hG hvw hvx hwx
  have huz_ne : u ≠ z := fun h => by subst h; exact G.asymm u v huv.1 hvz
  have hnzu : ¬ G.adj z u := fun hzu => hG ⟨u, v, z, huv.1, hvz, hzu⟩
  have hnuz : ¬ G.adj u z := fun huz =>
    G.sharp_claim1 hG hP1 huv huz hvz hvx hxz hux_ne hnux hnxu
  have hzb_ne : z ≠ b := fun h => by subst h; exact hnuz hub
  exact hP2 ⟨u, v, w, z, b, huz_ne, hvb_ne, hwz_ne, hzb_ne,
    huv.1, huw, hub, hvw.1, hvz, hwb, hnuz, hnzu, hnvb, hnbv, hnwz, hnzw⟩

/-- **Claim 4 (`K_{2,1}^N(u, w) = 0`)**: Uses ONLY `¬ P₁`, `¬ P₄`, `ih`, `hdeg` (ZERO 4-vertex `TC`!).
Applies `ih` to `X = N⁺(u) ∩ N⁺(w)` to find `x ∈ X` and `y ∈ N⁺(x) \ X`, killing `(u → y ∧ w → y)`! -/
private lemma sharp_claim4 (hG : G.TriangleFree) (hP1 : ¬ G.HasPattern1) (hP4 : ¬ G.HasPattern4)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    (hdeg : ∀ z : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg z)
    {u v w : V} (huv : G.IsCritArc u v) (hvw : G.IsCritArc v w)
    (huw_ind : u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u)
    {x₀ : V} (hux₀ : G.adj u x₀) (hwx₀ : G.adj w x₀) : False := by
  let X : Finset V := G.toDigraph.outSet u ∩ G.toDigraph.outSet w
  have hu_not : u ∉ X := fun h => G.loopless u ((Digraph.mem_outSet _).mp (Finset.mem_inter.mp h).1)
  have hX_lt : X.card < Fintype.card V := by
    calc X.card < (insert u X).card := by rw [Finset.card_insert_of_notMem hu_not]; omega
      _ ≤ Fintype.card V := Finset.card_le_univ _
  have hX_ne : X.Nonempty := ⟨x₀, Finset.mem_inter.mpr
    ⟨(Digraph.mem_outSet _).mpr hux₀, (Digraph.mem_outSet _).mpr hwx₀⟩⟩
  obtain ⟨x, hxX, hx_le⟩ := ih X hX_lt hX_ne
  have hux : G.adj u x := (Digraph.mem_outSet _).mp (Finset.mem_inter.mp hxX).1
  have hwx : G.adj w x := (Digraph.mem_outSet _).mp (Finset.mem_inter.mp hxX).2
  have hcard_lt : (X ∩ G.toDigraph.outSet x).card < (G.toDigraph.outSet x).card := by
    have hd := hdeg x
    change Fintype.card V ≤ 3 * (G.toDigraph.outSet x).card at hd
    have hX_pos : 1 ≤ X.card := Finset.one_le_card.mpr hX_ne
    omega
  have hnot_sub : ¬ (G.toDigraph.outSet x ⊆ X) := by
    intro hsub
    have heq : X ∩ G.toDigraph.outSet x = G.toDigraph.outSet x := Finset.inter_eq_right.mpr hsub
    rw [heq] at hcard_lt
    exact lt_irrefl _ hcard_lt
  obtain ⟨y, hy_x, hy_not_X⟩ := Finset.not_subset.mp hnot_sub
  have hxy : G.adj x y := (Digraph.mem_outSet _).mp hy_x
  have hnot_uw : ¬ (G.adj u y ∧ G.adj w y) := fun ⟨huy, hwy⟩ =>
    hy_not_X (Finset.mem_inter.mpr ⟨(Digraph.mem_outSet _).mpr huy, (Digraph.mem_outSet _).mpr hwy⟩)
  have hvx_ne : v ≠ x := fun h => by subst h; exact G.asymm v w hvw.1 hwx
  have hnxv : ¬ G.adj x v := fun hxv => hG ⟨v, w, x, hvw.1, hwx, hxv⟩
  have hnvx : ¬ G.adj v x := fun hvx =>
    G.sharp_claim1 hG hP1 huv hux hvx hvw.1 hwx huw_ind.1 huw_ind.2.1 huw_ind.2.2
  have hvy_ne : v ≠ y := fun h => by subst h; exact hnxv hxy
  have hnot_vw : ¬ (G.adj v y ∧ G.adj w y) := fun ⟨hvy, hwy⟩ =>
    G.sharp_claim1 hG hP1 hvw hvy hwy hwx hxy hvx_ne hnvx hnxv
  exact hP4 ⟨u, v, w, x, y, huw_ind.1, hvx_ne, hvy_ne,
    huv.1, hvw.1, hwx, hux, hxy, huw_ind.2.1, huw_ind.2.2, hnvx, hnxv, hnot_vw, hnot_uw⟩

/-- **Claim 5 (Subset Induction)**: Uses ONLY `¬ P₁, ¬ P₂, ¬ P₃, ¬ P₄`, `ih`, `hdeg`! -/
private lemma sharp_claim5 (hG : G.TriangleFree)
    (hP1 : ¬ G.HasPattern1) (hP2 : ¬ G.HasPattern2) (hP3 : ¬ G.HasPattern3) (hP4 : ¬ G.HasPattern4)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    (hdeg : ∀ z : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg z)
    {u v w : V} (huv : G.IsCritArc u v) (hvw : G.IsCritArc v w)
    (huw_ind : u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u) :
    3 * G.critOCnt u v + 1 ≤ G.critP3NCnt u w := by
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
    have hnwx : ¬ G.adj w x := fun hwx =>
      G.sharp_claim4 hG hP1 hP4 ih hdeg huv hvw huw_ind hux hwx
    by_cases hvx : G.adj v x
    · obtain ⟨z, huz, hxz, hvz_ne, hnvz, hnzv⟩ := G.exists_diff_out_of_crit hG huv hux hvx
      have hwz_ne : w ≠ z := fun h => by subst h; exact huw_ind.2.1 huz
      exact hP2 ⟨u, v, x, w, z, huw_ind.1, hvz_ne, hxw_ne, hwz_ne,
        huv.1, hux, huz, hvx, hvw.1, hxz, huw_ind.2.1, huw_ind.2.2, hnvz, hnzv, hnxw, hnwx⟩
    · have hvvstar : v ≠ vstar := fun h => by subst h; exact hvx hvstarx
      exact hP3 ⟨u, v, vstar, w, x, hvvstar, huw_ind.1, hxw_ne,
        huv.1, huvstar, hux, hvw.1, hvstarw, hvstarx, huw_ind.2.1, huw_ind.2.2, hnxw, hnwx, hvx⟩
  have hle1 : G.critOCnt u v ≤ G.critOCnt u vstar := huv.2 vstar huvstar
  have hle2 : G.critOCnt u vstar ≤ (U ∩ G.toDigraph.outSet vstar).card := Finset.card_le_card hsub
  have hU_pos : 1 ≤ U.card := Finset.one_le_card.mpr ⟨v, hvU⟩
  change 3 * G.critOCnt u v + 1 ≤ U.card
  omega

/-- **Claim 6 (Exact Integer Telescoping Inequality)**: Uses ONLY `¬ P₁..¬ P₄`, `ih`, `hdeg`! -/
private lemma sharp_claim6 (hG : G.TriangleFree)
    (hP1 : ¬ G.HasPattern1) (hP2 : ¬ G.HasPattern2) (hP3 : ¬ G.HasPattern3) (hP4 : ¬ G.HasPattern4)
    (ih : ∀ S : Finset V, S.card < Fintype.card V → S.Nonempty →
      ∃ z ∈ S, 3 * (S ∩ G.toDigraph.outSet z).card ≤ S.card - 1)
    (hdeg : ∀ z : V, Fintype.card V ≤ 3 * G.toDigraph.outDeg z)
    {u v w : V} (huv : G.IsCritArc u v) (hvw : G.IsCritArc v w)
    (huw_ind : u ≠ w ∧ ¬ G.adj u w ∧ ¬ G.adj w u) :
    (G.toDigraph.outDeg u : ℤ) + (G.toDigraph.outDeg v : ℤ) + (G.toDigraph.outDeg w : ℤ) +
      G.critPhiInt u v - G.critPhiInt v w ≤ (Fintype.card V : ℤ) - 1 := by
  have h5 : (3 * G.critOCnt u v + 1 : ℤ) ≤ (G.critP3NCnt u w : ℤ) := by
    exact_mod_cast G.sharp_claim5 hG hP1 hP2 hP3 hP4 ih hdeg huv hvw huw_ind
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
        (G.critBCnt u v : ℤ) - 2 * (G.critOCnt u v : ℤ) - (G.critOCnt v w : ℤ) - (G.critBCnt v w : ℤ) +
        (G.critP3NCnt u w : ℤ) = ∑ x : V, f x := by
    have hdu : (G.toDigraph.outDeg u : ℤ) = ∑ x : V, ind (G.adj u x) := hcard_sum _
    have hdv : (G.toDigraph.outDeg v : ℤ) = ∑ x : V, ind (G.adj v x) := hcard_sum _
    have hdw : (G.toDigraph.outDeg w : ℤ) = ∑ x : V, ind (G.adj w x) := hcard_sum _
    have hbuv : (G.critBCnt u v : ℤ) = ∑ x : V, ind (x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x) := hcard_sum _
    have hbvw : (G.critBCnt v w : ℤ) = ∑ x : V, ind (x ≠ v ∧ G.adj x w ∧ ¬ G.adj v x) := hcard_sum _
    have houv : (G.critOCnt u v : ℤ) = ∑ x : V, ind (G.adj u x ∧ G.adj v x) := by
      have : G.toDigraph.outSet u ∩ G.toDigraph.outSet v =
          Finset.univ.filter (fun x => G.adj u x ∧ G.adj v x) := by
        ext x; simp [Digraph.outSet]
      unfold critOCnt; rw [this]; exact hcard_sum _
    have hovw : (G.critOCnt v w : ℤ) = ∑ x : V, ind (G.adj v x ∧ G.adj w x) := by
      have : G.toDigraph.outSet v ∩ G.toDigraph.outSet w =
          Finset.univ.filter (fun x => G.adj v x ∧ G.adj w x) := by
        ext x; simp [Digraph.outSet]
      unfold critOCnt; rw [this]; exact hcard_sum _
    have hp3 : (G.critP3NCnt u w : ℤ) = ∑ x : V, ind (G.adj u x ∧ G.adj x w) := by
      have : G.toDigraph.outSet u ∩ G.toDigraph.inSet w =
          Finset.univ.filter (fun x => G.adj u x ∧ G.adj x w) := by
        ext x; simp [Digraph.outSet, Digraph.inSet]
      unfold critP3NCnt; rw [this]; exact hcard_sum _
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
      clear ih hdeg h5 hsum_eq
      split_ifs <;> simp_all
    · have hbuv' : ¬ (x ≠ u ∧ G.adj x v ∧ ¬ G.adj u x) := fun h => hbuv h.2
      by_cases hux : G.adj u x
      · have hnwx : ¬ G.adj w x := fun hwx => G.sharp_claim4 hG hP1 hP4 ih hdeg huv hvw huw_ind hux hwx
        clear ih hdeg h5 hsum_eq
        by_cases hxw : G.adj x w <;> by_cases hvx : G.adj v x <;> (split_ifs <;> simp_all)
      · clear ih hdeg h5 hsum_eq
        by_cases hvx : G.adj v x <;> by_cases hwx : G.adj w x <;> (split_ifs <;> simp_all)
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
  unfold critPhiInt
  linarith [h5, hsum_eq, htot]

end SharpProof

/-! ## Section 3: Master Zero-Four-Graph Exact `1/3` Theorem & Complete Hierarchy of Corollaries -/

/-- **ZERO-Four-Graph Conditional Exact `1/3` Caccetta–Häggkvist Theorem (2026)**:
Every finite nonempty `C₃`-free oriented graph `G` avoiding ONLY the four partial 5-vertex
patterns `P₁, P₂, P₃, P₄` (16 out of 317 five-vertex graphs; ZERO 4-vertex forbidden subgraphs;
covering `94.95%` of `F₅` and `77.72%` of `F₆` — nearly `3×` Razborov 2013!) contains a vertex `v`
with `3 * outDeg v ≤ |V| - 1`. -/
theorem exists_outDeg_le_third_of_forb_4patterns :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : OrientedGraph V) [DecidableRel G.adj],
      G.TriangleFree →
      ¬ G.HasPattern1 → ¬ G.HasPattern2 → ¬ G.HasPattern3 → ¬ G.HasPattern4 →
      ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 := by
  suffices hmain : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : OrientedGraph V) [DecidableRel G.adj],
      Fintype.card V = n →
      G.TriangleFree →
      ¬ G.HasPattern1 → ¬ G.HasPattern2 → ¬ G.HasPattern3 → ¬ G.HasPattern4 →
      ∃ v : V, 3 * G.toDigraph.outDeg v ≤ n - 1 by
    intro V _ _ _ G _ hG hP1 hP2 hP3 hP4
    exact hmain (Fintype.card V) G rfl hG hP1 hP2 hP3 hP4
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ hne G _ hn hG hP1 hP2 hP3 hP4
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
        (G.triangleFree_induce hG S) (G.not_hasPattern1_induce hP1 S)
        (G.not_hasPattern2_induce hP2 S) (G.not_hasPattern3_induce hP3 S)
        (G.not_hasPattern4_induce hP4 S)
      rw [G.outDeg_induce S ⟨u, hu⟩] at hu_le
      exact ⟨u, hu, hu_le⟩
    have hex_crit : ∀ v : V, ∃ w : V, G.IsCritArc v w := by
      intro v
      have hne_out : (G.toDigraph.outSet v).Nonempty := by
        have hd := hdeg v
        have hpos : 0 < Fintype.card V := Fintype.card_pos
        exact Finset.card_pos.mp (by unfold Digraph.outDeg at hd; omega)
      obtain ⟨w, hw_mem, hw_min⟩ := Finset.exists_min_image (G.toDigraph.outSet v) (G.critOCnt v) hne_out
      exact ⟨w, (Digraph.mem_outSet _).mp hw_mem, fun w' hw' => hw_min w' ((Digraph.mem_outSet _).mpr hw')⟩
    choose critNext hcritNext using hex_crit
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
    have hseq_crit : ∀ k : ℕ, G.IsCritArc (seq k) (seq (k + 1)) := by
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
    have hstep_ineq : ∀ k : ℕ,
        (G.toDigraph.outDeg (seq k) : ℤ) + (G.toDigraph.outDeg (seq (k + 1)) : ℤ) +
          (G.toDigraph.outDeg (seq (k + 2)) : ℤ) +
          G.critPhiInt (seq k) (seq (k + 1)) - G.critPhiInt (seq (k + 1)) (seq (k + 2)) ≤
        (Fintype.card V : ℤ) - 1 := by
      intro k
      have h1 := hseq_crit k
      have h2 := hseq_crit (k + 1)
      have hind := G.sharp_claim3 hG hP1 hP2 hih_sub hdeg h1 h2
      exact G.sharp_claim6 hG hP1 hP2 hP3 hP4 hih_sub hdeg h1 h2 hind
    have hsum_le :
        ∑ k ∈ Finset.range ℓ,
          ((G.toDigraph.outDeg (seq k) : ℤ) + (G.toDigraph.outDeg (seq (k + 1)) : ℤ) +
            (G.toDigraph.outDeg (seq (k + 2)) : ℤ) +
            G.critPhiInt (seq k) (seq (k + 1)) - G.critPhiInt (seq (k + 1)) (seq (k + 2))) ≤
        (ℓ : ℤ) * ((Fintype.card V : ℤ) - 1) := by
      calc ∑ k ∈ Finset.range ℓ, _
          ≤ ∑ _k ∈ Finset.range ℓ, ((Fintype.card V : ℤ) - 1) :=
            Finset.sum_le_sum fun k _ => hstep_ineq k
        _ = (ℓ : ℤ) * ((Fintype.card V : ℤ) - 1) := by simp; ring
    have hshift : ∀ (F : V → ℤ),
        ∑ k ∈ Finset.range ℓ, F (seq (k + 1)) = ∑ k ∈ Finset.range ℓ, F (seq k) := by
      intro F
      have h1 := Finset.sum_range_succ (fun k => F (seq k)) ℓ
      have h2 := Finset.sum_range_succ' (fun k => F (seq k)) ℓ
      have hper0 : seq ℓ = seq 0 := by simpa using hseq_per 0
      linarith [h1, h2, congrArg F hper0]
    have htele : ∑ k ∈ Finset.range ℓ,
        (G.critPhiInt (seq k) (seq (k + 1)) - G.critPhiInt (seq (k + 1)) (seq (k + 2))) = 0 := by
      have h1 := Finset.sum_range_sub' (fun k => G.critPhiInt (seq k) (seq (k + 1))) ℓ
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
              G.critPhiInt (seq k) (seq (k + 1)) - G.critPhiInt (seq (k + 1)) (seq (k + 2))) =
          (∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq k) : ℤ)) +
          (∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 1)) : ℤ)) +
          (∑ k ∈ Finset.range ℓ, (G.toDigraph.outDeg (seq (k + 2)) : ℤ)) +
          ∑ k ∈ Finset.range ℓ,
            (G.critPhiInt (seq k) (seq (k + 1)) - G.critPhiInt (seq (k + 1)) (seq (k + 2))) := by
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

/-- **1-Four-Graph Corollary (Dropping `OP` and `IP` completely; `58.53%` of `F₆`, `89.94%` of `TC`-free!)**:
Forbids `TC` + 3 partial 5-vertex patterns (`F₅⁽¹⁾`, `P₂`, `P₃` = 6 `TC`-free five-graphs). -/
theorem exists_outDeg_le_third_of_forb_TC_P1_P2_P3
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hF5 : ¬ G.HasInducedF5_1)
    (hP2 : ¬ G.HasPattern2) (hP3 : ¬ G.HasPattern3) :
    ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 :=
  exists_outDeg_le_third_of_forb_4patterns G hG
    (not_hasPattern1_of_not_TC_F5 hG hTC hF5) hP2 hP3 (fun h => hTC (hasInducedTC_of_hasPattern4 h))

/-- **1-Four-Graph Corollary (Dropping `TC` and `IP` completely; `53.61%` of `F₆`!)**:
Forbids `OP` + 2 partial 5-vertex patterns (`P₁`, `P₄` = 9 five-graphs). -/
theorem exists_outDeg_le_third_of_forb_OP_P1_P4
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) (hOP : ¬ G.HasInducedOP)
    (hP1 : ¬ G.HasPattern1) (hP4 : ¬ G.HasPattern4) :
    ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 :=
  exists_outDeg_le_third_of_forb_4patterns G hG
    hP1 (fun h => hOP (hasInducedOP_of_hasPattern2 h))
    (fun h => hOP (hasInducedOP_of_hasPattern3 h)) hP4

/-- **Stage-3 Corollary** recovered in 2 lines from the Zero-Four-Graph theorem. -/
theorem exists_outDeg_le_third_of_forb_TC_OP_F5_sharp
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hOP : ¬ G.HasInducedOP) (hF5 : ¬ G.HasInducedF5_1) :
    ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 :=
  exists_outDeg_le_third_of_forb_TC_P1_P2_P3 G hG hTC hF5
    (fun h => hOP (hasInducedOP_of_hasPattern2 h))
    (fun h => hOP (hasInducedOP_of_hasPattern3 h))

/-- **Razborov (2013) Corollary** recovered in 2 lines from the Zero-Four-Graph theorem. -/
theorem exists_outDeg_le_third_of_razborov_sharp
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) (hTC : ¬ G.HasInducedTC) (hOP : ¬ G.HasInducedOP) (hIP : ¬ G.HasInducedIP) :
    ∃ v : V, 3 * G.toDigraph.outDeg v ≤ Fintype.card V - 1 :=
  exists_outDeg_le_third_of_forb_TC_OP_F5_sharp G hG hTC hOP
    (fun h => hIP (hasInducedIP_of_hasInducedF5_1 h))

end OrientedGraph

/-- Wrapper for general simple `Digraph V` under `¬ G.HasCycleLe3`. -/
theorem Digraph.exists_outDeg_le_third_of_forb_4patterns
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : Digraph V) [dG : DecidableRel G.adj] (h3free : ¬ G.HasCycleLe3)
    (hP1 : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasPattern1)
    (hP2 : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasPattern2)
    (hP3 : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasPattern3)
    (hP4 : ¬ (G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))).HasPattern4) :
    ∃ v : V, 3 * G.outDeg v ≤ Fintype.card V - 1 := by
  let H : OrientedGraph V := G.toOrientedOfNotHasDigon (fun hd => h3free (Or.inl hd))
  let _ : DecidableRel H.adj := dG
  exact H.exists_outDeg_le_third_of_forb_4patterns (fun ht => h3free (Or.inr ht)) hP1 hP2 hP3 hP4

/-! ## Section 4: Complete Sharpness Characterization — Explicit Finite Obstructions for All 4 Patterns -/

namespace SharpObstructions

/-- **Sharp `P₁` Obstruction (`Fin 6`, 10 arcs)**:
`C₃`-free, `{TC, OP, P₂, P₃, P₄}`-free, with critical arc `0 → 5` violating Claim 1 (`x = 3, y = 1`). -/
def adjP1 (a b : Fin 6) : Bool :=
  (a == 0 && (b == 2 || b == 3 || b == 4 || b == 5)) ||
  (a == 1 && b == 3) ||
  (a == 2 && b == 5) ||
  (a == 3 && b == 4) ||
  (a == 4 && b == 2) ||
  (a == 5 && (b == 1 || b == 3))

def graphP1 : OrientedGraph (Fin 6) where
  adj a b := adjP1 a b = true
  loopless := by decide
  asymm := by decide

instance : DecidableRel graphP1.adj := fun a b => inferInstanceAs (Decidable (adjP1 a b = true))

theorem obstructionP1_sharp :
    graphP1.TriangleFree ∧
    ¬ graphP1.HasInducedTC ∧ ¬ graphP1.HasInducedOP ∧
    ¬ graphP1.HasPattern2 ∧ ¬ graphP1.HasPattern3 ∧ ¬ graphP1.HasPattern4 ∧
    graphP1.HasPattern1 ∧
    graphP1.IsCritArc 0 5 ∧
    (graphP1.adj 0 3 ∧ graphP1.adj 5 3 ∧ graphP1.adj 5 1 ∧ graphP1.adj 1 3 ∧
      (0 : Fin 6) ≠ 1 ∧ ¬ graphP1.adj 0 1 ∧ ¬ graphP1.adj 1 0) := by
  have htri : graphP1.TriangleFree := by
    rintro ⟨a, b, c, h1, h2, h3⟩; revert a b c h1 h2 h3; decide
  have hTC : ¬ graphP1.HasInducedTC := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hOP : ¬ graphP1.HasInducedOP := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  refine ⟨htri, hTC, hOP,
    fun h => hOP (OrientedGraph.hasInducedOP_of_hasPattern2 h),
    fun h => hOP (OrientedGraph.hasInducedOP_of_hasPattern3 h),
    fun h => hTC (OrientedGraph.hasInducedTC_of_hasPattern4 h),
    ⟨0, 5, 3, 1, 4, by decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    by decide⟩

/-- **Sharp `P₂` Obstruction (`Fin 6`, 9 arcs)**:
`C₃`-free, `{TC, IP, P₁, P₃, P₄}`-free, with critical arcs `5 → 4`, `4 → 1`, `4 → 2` violating BOTH
Claim 3 (`5 → 1`, with Claim-2 witness `x = 2`) AND Claim 5 (`3 * o(5, 4) + 1 = 4 > 1 = p3N(5, 2)`). -/
def adjP2 (a b : Fin 6) : Bool :=
  (a == 0 && b == 4) ||
  (a == 1 && b == 3) ||
  (a == 3 && b == 0) ||
  (a == 4 && (b == 1 || b == 2)) ||
  (a == 5 && (b == 0 || b == 1 || b == 3 || b == 4))

def graphP2 : OrientedGraph (Fin 6) where
  adj a b := adjP2 a b = true
  loopless := by decide
  asymm := by decide

instance : DecidableRel graphP2.adj := fun a b => inferInstanceAs (Decidable (adjP2 a b = true))

theorem obstructionP2_sharp :
    graphP2.TriangleFree ∧
    ¬ graphP2.HasInducedTC ∧ ¬ graphP2.HasInducedIP ∧
    ¬ graphP2.HasPattern1 ∧ ¬ graphP2.HasPattern3 ∧ ¬ graphP2.HasPattern4 ∧
    graphP2.HasPattern2 ∧
    graphP2.IsCritArc 5 4 ∧ graphP2.IsCritArc 4 1 ∧ graphP2.adj 5 1 ∧
    graphP2.IsCritArc 4 2 ∧ ((5 : Fin 6) ≠ 2 ∧ ¬ graphP2.adj 5 2 ∧ ¬ graphP2.adj 2 5) ∧
    3 * graphP2.critOCnt 5 4 + 1 > graphP2.critP3NCnt 5 2 := by
  have htri : graphP2.TriangleFree := by
    rintro ⟨a, b, c, h1, h2, h3⟩; revert a b c h1 h2 h3; decide
  have hTC : ¬ graphP2.HasInducedTC := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hIP : ¬ graphP2.HasInducedIP := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hP3 : ¬ graphP2.HasPattern3 := by
    rintro ⟨u, v, v', w, x, h⟩; revert u v v' w x h; decide
  refine ⟨htri, hTC, hIP,
    OrientedGraph.not_hasPattern1_of_not_TC_F5 htri hTC (fun h => hIP (OrientedGraph.hasInducedIP_of_hasInducedF5_1 h)),
    hP3,
    fun h => hTC (OrientedGraph.hasInducedTC_of_hasPattern4 h),
    ⟨5, 4, 1, 2, 3, by decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    by decide,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    by decide, by decide⟩

/-- **Sharp `P₃` Obstruction (`Fin 8`, 17 arcs, `C₄` inside `N⁺(u) ∩ N⁺(v*) \ U`)**:
`C₃`-free, `{TC, IP, P₁, P₂, P₄}`-free, with critical arcs `0 → 1` and `1 → 3` (`0 ⊥ 3`),
violating Claim 5 (`3 * o(0, 1) + 1 = 4 > 2 = p3N(0, 3)`). -/
def adjP3 (a b : Fin 8) : Bool :=
  (a == 0 && (b == 1 || b == 2 || b == 4 || b == 5 || b == 6 || b == 7)) ||
  (a == 1 && (b == 2 || b == 3)) ||
  (a == 2 && (b == 3 || b == 4 || b == 5 || b == 6 || b == 7)) ||
  (a == 4 && b == 5) ||
  (a == 5 && b == 6) ||
  (a == 6 && b == 7) ||
  (a == 7 && b == 4)

def graphP3 : OrientedGraph (Fin 8) where
  adj a b := adjP3 a b = true
  loopless := by decide
  asymm := by decide

instance : DecidableRel graphP3.adj := fun a b => inferInstanceAs (Decidable (adjP3 a b = true))

theorem obstructionP3_sharp :
    graphP3.TriangleFree ∧
    ¬ graphP3.HasInducedTC ∧ ¬ graphP3.HasInducedIP ∧
    ¬ graphP3.HasPattern1 ∧ ¬ graphP3.HasPattern2 ∧ ¬ graphP3.HasPattern4 ∧
    graphP3.HasPattern3 ∧
    graphP3.IsCritArc 0 1 ∧ graphP3.IsCritArc 1 3 ∧
    ((0 : Fin 8) ≠ 3 ∧ ¬ graphP3.adj 0 3 ∧ ¬ graphP3.adj 3 0) ∧
    3 * graphP3.critOCnt 0 1 + 1 > graphP3.critP3NCnt 0 3 := by
  have htri : graphP3.TriangleFree := by
    rintro ⟨a, b, c, h1, h2, h3⟩; revert a b c h1 h2 h3; decide
  have hTC : ¬ graphP3.HasInducedTC := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hIP : ¬ graphP3.HasInducedIP := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hP2 : ¬ graphP3.HasPattern2 := by
    rintro ⟨u, v, w, x, z, hux_ne, hvz_ne, hwx_ne, hxz_ne, huv, huw, huz, hvw, hvx, hwz,
      hnux, hnxu, hnvz, hnzv, hnwx, hnxw⟩
    have hu02_all : ∀ u v w z : Fin 8,
        graphP3.adj u v → graphP3.adj u w → graphP3.adj u z →
        v ≠ w → v ≠ z → w ≠ z → u = 0 ∨ u = 2 := by decide
    have hu02 : u = 0 ∨ u = 2 :=
      hu02_all u v w z huv huw huz (graphP3.ne_of_adj hvw) hvz_ne (graphP3.ne_of_adj hwz)
    rcases hu02 with rfl | rfl
    · have hx3_all : ∀ x : Fin 8,
          (0 : Fin 8) ≠ x → ¬ graphP3.adj 0 x → ¬ graphP3.adj x 0 → x = 3 := by decide
      have hx3 : x = 3 := hx3_all x hux_ne hnux hnxu
      subst hx3
      have h0_contra : ∀ v w z : Fin 8,
          graphP3.adj 0 v → graphP3.adj 0 w → graphP3.adj 0 z →
          graphP3.adj v w → graphP3.adj v 3 → graphP3.adj w z →
          v ≠ z → ¬ graphP3.adj v z → ¬ graphP3.adj z v →
          ¬ graphP3.adj w 3 → ¬ graphP3.adj 3 w → False := by decide
      exact h0_contra v w z huv huw huz hvw hvx hwz hvz_ne hnvz hnzv hnwx hnxw
    · have h2_contra : ∀ v x : Fin 8,
          graphP3.adj 2 v → graphP3.adj v x → ¬ graphP3.adj 2 x → False := by decide
      exact h2_contra v x huv hvx hnux
  refine ⟨htri, hTC, hIP,
    OrientedGraph.not_hasPattern1_of_not_TC_F5 htri hTC (fun h => hIP (OrientedGraph.hasInducedIP_of_hasInducedF5_1 h)),
    hP2,
    fun h => hTC (OrientedGraph.hasInducedTC_of_hasPattern4 h),
    ⟨0, 1, 2, 3, 4, by decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    by decide, by decide⟩

/-- **Sharp `P₄` (`TC⁺`) Obstruction (`Fin 6`, 7 arcs, `δ⁺ = 1`, NO sinks!)**:
`C₃`-free, `{OP, IP, P₁, P₂, P₃}`-free, with `∀ v, 1 ≤ outDeg v`, critical arcs `2 → 5` and `5 → 1`
(`2 ⊥ 1`), violating BOTH Claim 4 (`4 ∈ N⁺(2) ∩ N⁺(1)`) AND Claim 6
(`d⁺(2) + d⁺(5) + d⁺(1) + φ(2, 5) - φ(5, 1) = 6 > 5 = |V| - 1`)! -/
def adjP4 (a b : Fin 6) : Bool :=
  (a == 0 && b == 5) ||
  (a == 1 && b == 4) ||
  (a == 2 && (b == 4 || b == 5)) ||
  (a == 3 && b == 5) ||
  (a == 4 && b == 0) ||
  (a == 5 && b == 1)

def graphP4 : OrientedGraph (Fin 6) where
  adj a b := adjP4 a b = true
  loopless := by decide
  asymm := by decide

instance : DecidableRel graphP4.adj := fun a b => inferInstanceAs (Decidable (adjP4 a b = true))

theorem obstructionP4_sharp :
    graphP4.TriangleFree ∧
    (∀ v : Fin 6, 1 ≤ graphP4.toDigraph.outDeg v) ∧
    ¬ graphP4.HasInducedOP ∧ ¬ graphP4.HasInducedIP ∧
    ¬ graphP4.HasPattern1 ∧ ¬ graphP4.HasPattern2 ∧ ¬ graphP4.HasPattern3 ∧
    graphP4.HasPattern4 ∧
    graphP4.IsCritArc 2 5 ∧ graphP4.IsCritArc 5 1 ∧
    ((2 : Fin 6) ≠ 1 ∧ ¬ graphP4.adj 2 1 ∧ ¬ graphP4.adj 1 2) ∧
    (graphP4.adj 2 4 ∧ graphP4.adj 1 4) ∧
    (graphP4.toDigraph.outDeg 2 : ℤ) + (graphP4.toDigraph.outDeg 5 : ℤ) +
      (graphP4.toDigraph.outDeg 1 : ℤ) + graphP4.critPhiInt 2 5 - graphP4.critPhiInt 5 1 >
      (Fintype.card (Fin 6) : ℤ) - 1 := by
  have htri : graphP4.TriangleFree := by
    rintro ⟨a, b, c, h1, h2, h3⟩; revert a b c h1 h2 h3; decide
  have hOP : ¬ graphP4.HasInducedOP := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hIP : ¬ graphP4.HasInducedIP := by
    rintro ⟨a, b, c, d, h⟩; revert a b c d h; decide
  have hP1 : ¬ graphP4.HasPattern1 := by
    rintro ⟨v, w, x, y, z, h⟩; revert v w x y z h; decide
  refine ⟨htri,
    fun v => by revert v; decide,
    hOP, hIP, hP1,
    fun h => hOP (OrientedGraph.hasInducedOP_of_hasPattern2 h),
    fun h => hOP (OrientedGraph.hasInducedOP_of_hasPattern3 h),
    ⟨2, 5, 1, 4, 0, by decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    ⟨by decide, fun w hw => by revert w hw; decide⟩,
    by decide, by decide, by decide⟩

end SharpObstructions

end CaccettaHaggkvist
