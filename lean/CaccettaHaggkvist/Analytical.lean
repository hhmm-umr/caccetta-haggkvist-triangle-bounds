module

public import CaccettaHaggkvist.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Analytical Bounds for the Caccetta–Häggkvist Conjecture (`k = 3`)

This module proves unconditionally (for ALL finite simple directed graphs `Digraph V` on `|V| ≥ 1`
vertices, with zero `sorry` and standard axioms only):
1. **Caccetta–Häggkvist Inductively Tight Quadratic Bound (`c = (3 - √5) / 2 ≈ 0.38196601`)**:
   Every finite simple digraph `G` on `|V| ≥ 1` vertices with
   `∀ u, (G.outDeg u : ℝ) ≥ ((3 - Real.sqrt 5) / 2) * |V|`
   contains a directed cycle of length at most `3` (`G.HasCycleLe3`).
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

namespace OrientedGraph

/-- Induced oriented subgraph on a subset `S : Finset V`. -/
def induce {V : Type u} (G : OrientedGraph V) (S : Finset V) :
    OrientedGraph {x : V // x ∈ S} where
  adj x y := G.adj x.1 y.1
  loopless x := G.loopless x.1
  asymm x y := G.asymm x.1 y.1

instance instDecidableRelInduce {V : Type u} (G : OrientedGraph V) [h : DecidableRel G.adj]
    (S : Finset V) : DecidableRel (G.induce S).adj :=
  fun x y => h x.1 y.1

lemma triangleFree_induce {V : Type u} {G : OrientedGraph V}
    (hG : G.TriangleFree) (S : Finset V) : (G.induce S).TriangleFree := by
  rintro ⟨u, v, w, huv, hvw, hwu⟩
  exact hG ⟨u.1, v.1, w.1, huv, hvw, hwu⟩

lemma outDeg_induce {V : Type u} [Fintype V] [DecidableEq V]
    (G : OrientedGraph V) [DecidableRel G.adj] (S : Finset V) (x : {z : V // z ∈ S}) :
    (G.induce S).toDigraph.outDeg x = (S ∩ G.toDigraph.outSet x.1).card := by
  have hmap :
      ((G.induce S).toDigraph.outSet x).map ⟨Subtype.val, Subtype.val_injective⟩ =
        S ∩ G.toDigraph.outSet x.1 := by
    ext z
    simp only [Finset.mem_map, Digraph.mem_outSet, Finset.mem_inter]
    constructor
    · rintro ⟨⟨z', hz'⟩, hxz', rfl⟩
      exact ⟨hz', hxz'⟩
    · rintro ⟨hz, hxz⟩
      exact ⟨⟨z, hz⟩, hxz, rfl⟩
  rw [← hmap, Finset.card_map]
  rfl

/-- Key `C₃`-free neighborhood disjointness inequality along any directed edge `u → v`:
`{u}`, `N⁺(u)`, `N⁻(u)`, and `N⁺(v) \ N⁺(u)` are pairwise disjoint subsets of `V`. -/
lemma card_bound_of_adj_triangleFree {V : Type u} [Fintype V] [DecidableEq V]
    {G : OrientedGraph V} [DecidableRel G.adj] (hG : G.TriangleFree)
    {u v : V} (huv : G.adj u v) :
    1 + G.toDigraph.outDeg u + G.toDigraph.inDeg u + G.toDigraph.outDeg v ≤
      Fintype.card V + (G.toDigraph.outSet u ∩ G.toDigraph.outSet v).card := by
  let A : Finset V := insert u (G.toDigraph.outSet u ∪ G.toDigraph.inSet u)
  let B : Finset V := G.toDigraph.outSet v \ G.toDigraph.outSet u
  have hu_not : u ∉ G.toDigraph.outSet u ∪ G.toDigraph.inSet u := by
    simp [G.loopless u]
  have hA_card : A.card = 1 + G.toDigraph.outDeg u + G.toDigraph.inDeg u := by
    rw [Finset.card_insert_of_notMem hu_not,
      Finset.card_union_of_disjoint (G.disjoint_outSet_inSet u)]
    dsimp [Digraph.outDeg, Digraph.inDeg]
    omega
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [Finset.mem_sdiff, Digraph.mem_outSet, Digraph.mem_outSet] at hwB
    rcases hwB with ⟨hvw, hn_uw⟩
    simp only [A, Finset.mem_insert, Finset.mem_union, Digraph.mem_outSet,
      Digraph.mem_inSet] at hwA
    rcases hwA with hwu_eq | huw | hwu
    · rw [hwu_eq] at hvw
      exact G.asymm u v huv hvw
    · exact hn_uw huw
    · exact hG ⟨u, v, w, huv, hvw, hwu⟩
  have hAB_le : A.card + B.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hAB_disj]
    exact Finset.card_le_univ _
  have hB_split :
      B.card + (G.toDigraph.outSet u ∩ G.toDigraph.outSet v).card = G.toDigraph.outDeg v := by
    dsimp [B, Digraph.outDeg]
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter _ _
  omega

end OrientedGraph

/-- Average in-degree equals average out-degree: if every vertex has out-degree at least `b`,
some vertex has in-degree at least `b`. -/
lemma Digraph.exists_inDeg_ge_of_outDeg_ge {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj] {b : ℝ}
    (hdeg : ∀ x : V, b ≤ (G.outDeg x : ℝ)) :
    ∃ u : V, b ≤ (G.inDeg u : ℝ) := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ (Finset.univ : Finset V), (G.inDeg x : ℝ) < (G.outDeg x : ℝ) :=
    fun x _ => lt_of_lt_of_le (hno x) (hdeg x)
  have hsum_lt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
  have hsum_eq : ∑ x : V, (G.outDeg x : ℝ) = ∑ x : V, (G.inDeg x : ℝ) := by
    exact_mod_cast G.sum_outDeg_eq_sum_inDeg
  linarith

/-- Strong-induction bound for any constant `c ∈ (0, 1)` satisfying `3c - c² ≥ 1`. -/
theorem OrientedGraph.exists_outDeg_lt_of_quadratic {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hcq : 1 ≤ 3 * c - c ^ 2) :
    ∀ {V : Type u} [Fintype V] [Nonempty V] (G : OrientedGraph V) [DecidableRel G.adj],
      G.TriangleFree → ∃ u : V, (G.toDigraph.outDeg u : ℝ) < c * Fintype.card V := by
  suffices hmain : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [Nonempty V]
      (G : OrientedGraph V) [DecidableRel G.adj],
      Fintype.card V = n → G.TriangleFree →
      ∃ u : V, (G.toDigraph.outDeg u : ℝ) < c * Fintype.card V by
    intro V _ _ G _ hG
    exact hmain (Fintype.card V) G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ G _ hn hG
    let _ : DecidableEq V := Classical.decEq V
    by_contra hno
    push Not at hno
    have hn_pos : 0 < n := hn ▸ Fintype.card_pos
    have hcn_pos : 0 < c * (n : ℝ) := mul_pos hc0 (Nat.cast_pos.mpr hn_pos)
    have hdeg_n : ∀ x : V, c * (n : ℝ) ≤ (G.toDigraph.outDeg x : ℝ) := by
      intro x
      simpa [hn] using hno x
    obtain ⟨u, hin_u⟩ := G.toDigraph.exists_inDeg_ge_of_outDeg_ge hdeg_n
    let S : Finset V := G.toDigraph.outSet u
    have hdu_ge : c * (n : ℝ) ≤ (G.toDigraph.outDeg u : ℝ) := hdeg_n u
    have hS_pos_real : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hcn_pos hdu_ge
    have hS_pos : 0 < S.card := Nat.cast_pos.mp hS_pos_real
    have _ : Nonempty {z : V // z ∈ S} := Finset.Nonempty.to_subtype (Finset.card_pos.mp hS_pos)
    have hu_not_S : u ∉ S := G.toDigraph.notMem_outSet_self u
    have hS_lt : S.card < n := by
      rw [← hn]
      calc S.card < (insert u S).card := by
            rw [Finset.card_insert_of_notMem hu_not_S]
            omega
        _ ≤ Fintype.card V := Finset.card_le_univ _
    have hcard_sub : Fintype.card {z : V // z ∈ S} = S.card := Fintype.card_coe S
    obtain ⟨v, hv_lt⟩ := ih S.card hS_lt (G.induce S) hcard_sub (G.triangleFree_induce hG S)
    rw [G.outDeg_induce S v, hcard_sub] at hv_lt
    have huv : G.adj u v.1 := (G.toDigraph.mem_outSet).mp v.2
    have hcard_ineq :
        (1 : ℝ) + (G.toDigraph.outDeg u : ℝ) + (G.toDigraph.inDeg u : ℝ) +
          (G.toDigraph.outDeg v.1 : ℝ) ≤
        (n : ℝ) + ((S ∩ G.toDigraph.outSet v.1).card : ℝ) := by
      have hnat := G.card_bound_of_adj_triangleFree hG huv
      rw [hn] at hnat
      exact_mod_cast hnat
    have hdv_ge : c * (n : ℝ) ≤ (G.toDigraph.outDeg v.1 : ℝ) := hdeg_n v.1
    have hp1 : 0 ≤ (1 - c) * ((G.toDigraph.outDeg u : ℝ) - c * (n : ℝ)) :=
      mul_nonneg (sub_pos.mpr hc1).le (sub_nonneg.mpr hdu_ge)
    have hp2 : (n : ℝ) ≤ (3 * c - c ^ 2) * (n : ℝ) := by
      nlinarith [hcq, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hS_eq : (S.card : ℝ) = (G.toDigraph.outDeg u : ℝ) := rfl
    rw [hS_eq] at hv_lt
    nlinarith

/-- The classical Caccetta–Häggkvist (1978) constant `(3 - √5) / 2 ≈ 0.38196601`. -/
noncomputable def chConstant : ℝ := (3 - Real.sqrt 5) / 2

lemma chConstant_pos : 0 < chConstant := by
  unfold chConstant
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma chConstant_lt_one : chConstant < 1 := by
  unfold chConstant
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma chConstant_quadratic : 3 * chConstant - chConstant ^ 2 = 1 := by
  unfold chConstant
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- **Caccetta–Häggkvist (1978) Analytical Bound for Oriented Graphs**:
Every finite nonempty `C₃`-free oriented graph `G` has a vertex of out-degree strictly less than
`((3 - √5) / 2) * |V|`. -/
theorem OrientedGraph.exists_outDeg_lt_chConstant {V : Type u} [Fintype V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj] (hG : G.TriangleFree) :
    ∃ u : V, (G.toDigraph.outDeg u : ℝ) < chConstant * Fintype.card V :=
  OrientedGraph.exists_outDeg_lt_of_quadratic chConstant_pos chConstant_lt_one
    chConstant_quadratic.symm.le G hG

/-- **Caccetta–Häggkvist (1978) Analytical Theorem for ALL Simple Directed Graphs**:
Every finite nonempty simple digraph `G` with minimum out-degree at least `((3 - √5) / 2) * |V|`
contains a directed cycle of length at most `3`. -/
theorem hasCycleLe3_of_minOutDeg_ge_chConstant {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj]
    (hdeg : ∀ u : V, chConstant * Fintype.card V ≤ (G.outDeg u : ℝ)) :
    G.HasCycleLe3 :=
  hasCycleLe3_of_oriented_bound
    (fun H d hH => @OrientedGraph.exists_outDeg_lt_chConstant V _ _ H d hH)
    G hdeg

end CaccettaHaggkvist
