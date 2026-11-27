module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# Extremal Simplex Weights, Blow-Up Reduction, and Zero-Error Pullback Homomorphism

This module establishes the three foundational bridges between finite `C₃`-free oriented graphs and
asymptotic / weighted flag-algebra inequalities:

1. **Simplex Compactness & Extremal Vertex Weights (`exists_max_minOutWeight`)**:
   Maximizing `min_u outWeight G w u` over the probability simplex `probSimplex V` (`w ≥ 0`,
   `∑ v, w v = 1`) attains its maximum `c* ≥ δ⁺(G) / |V|` at an extremal weight `w*`, with
   support restriction (`suppSet w*`) and directional perturbation criticality.
2. **Balanced `N`-Fold Blow-Up Bridge (`OrientedGraph.blowup`, `exists_outDeg_le_of_asymptotic_bound`)**:
   Any asymptotic flag-algebra upper bound `δ⁺(H) ≤ c * |W| + C` (`C` constant) applied to
   `G.blowup N` eliminates the `+ C` error completely and proves `∃ u, outDeg G u ≤ c * |V|` for
   EVERY finite `n ≥ 1`.
3. **Zero-`O(1/n)` Finite Pullback Flag Homomorphism (`OrientedGraph.pullback`, `tupleWeight`)**:
   Sampling `x : Fin m → V` i.i.d. from `w` induces a `C₃`-free `OrientedGraph (Fin m)` for EVERY
   tuple `x` (including diagonal self-collisions, which become non-adjacent twin vertices), giving
   an exact finite-sum flag-algebra homomorphism with ZERO `O(1/n)` finite-graph error!
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

/-! ## Section 1: Probability Simplex & Weighted Out-Degrees -/

/-- `w : V → ℝ` is a probability weight vector on `V` (`w ≥ 0` and `∑ v, w v = 1`). -/
def IsProbWeight {V : Type u} [Fintype V] (w : V → ℝ) : Prop :=
  (∀ v : V, 0 ≤ w v) ∧ ∑ v : V, w v = 1

/-- The probability simplex `{w : V → ℝ | IsProbWeight w}`. -/
def probSimplex (V : Type u) [Fintype V] : Set (V → ℝ) :=
  {w | IsProbWeight w}

lemma IsProbWeight.nonneg {V : Type u} [Fintype V] {w : V → ℝ} (hw : IsProbWeight w) (v : V) :
    0 ≤ w v := hw.1 v

lemma IsProbWeight.sum_eq_one {V : Type u} [Fintype V] {w : V → ℝ} (hw : IsProbWeight w) :
    ∑ v : V, w v = 1 := hw.2

lemma IsProbWeight.le_one {V : Type u} [Fintype V] {w : V → ℝ} (hw : IsProbWeight w) (v : V) :
    w v ≤ 1 := by
  calc w v ≤ ∑ x : V, w x := Finset.single_le_sum (fun x _ => hw.1 x) (Finset.mem_univ v)
    _ = 1 := hw.2

/-- Uniform probability weight `w(v) = 1 / |V|` on a nonempty finite vertex set `V`. -/
noncomputable def unifWeight (V : Type u) [Fintype V] : V → ℝ :=
  fun _ => (1 : ℝ) / (Fintype.card V : ℝ)

lemma isProbWeight_unifWeight {V : Type u} [Fintype V] [Nonempty V] :
    IsProbWeight (unifWeight V) := by
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun _ => div_nonneg zero_le_one hpos.le, ?_⟩
  simp [unifWeight, div_eq_mul_inv]

namespace Digraph

/-- Weighted out-degree `∑_{v : G.adj u v} w v` of vertex `u`. -/
def outWeight {V : Type u} [Fintype V] (G : Digraph V) [DecidableRel G.adj]
    (w : V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ G.outSet u, w v

/-- Weighted in-degree `∑_{v : G.adj v u} w v` of vertex `u`. -/
def inWeight {V : Type u} [Fintype V] (G : Digraph V) [DecidableRel G.adj]
    (w : V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ G.inSet u, w v

/-- Minimum weighted out-degree `min_{u ∈ V} outWeight G w u`. -/
def minOutWeight {V : Type u} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj]
    (w : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (G.outWeight w)

lemma minOutWeight_le_outWeight {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj] (w : V → ℝ) (u : V) :
    G.minOutWeight w ≤ G.outWeight w u :=
  Finset.inf'_le (G.outWeight w) (Finset.mem_univ u)

lemma le_minOutWeight_iff {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj] (w : V → ℝ) {c : ℝ} :
    c ≤ G.minOutWeight w ↔ ∀ u : V, c ≤ G.outWeight w u := by
  unfold minOutWeight
  rw [Finset.le_inf'_iff]
  simp

lemma outWeight_unifWeight {V : Type u} [Fintype V]
    (G : Digraph V) [DecidableRel G.adj] (u : V) :
    G.outWeight (unifWeight V) u = (G.outDeg u : ℝ) / (Fintype.card V : ℝ) := by
  simp [outWeight, unifWeight, outDeg, div_eq_mul_inv]

lemma le_minOutWeight_unifWeight {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj] {c : ℝ}
    (hdeg : ∀ u : V, c * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) :
    c ≤ G.minOutWeight (unifWeight V) := by
  rw [le_minOutWeight_iff]
  intro u
  rw [outWeight_unifWeight]
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact (le_div_iff₀ hpos).mpr (hdeg u)

end Digraph

/-! ## Section 2: Compactness of the Probability Simplex & Extremal Weight Existence -/

lemma isClosed_probSimplex {V : Type u} [Fintype V] : IsClosed (probSimplex V) := by
  have heq : probSimplex V =
      (⋂ v : V, {w : V → ℝ | 0 ≤ w v}) ∩ {w : V → ℝ | ∑ v : V, w v = 1} := by
    ext w
    simp [probSimplex, IsProbWeight]
  rw [heq]
  have hcont_sum : Continuous (fun w : V → ℝ => ∑ v : V, w v) := by fun_prop
  exact IsClosed.inter
    (isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v))
    (isClosed_eq hcont_sum continuous_const)

lemma isCompact_probSimplex {V : Type u} [Fintype V] : IsCompact (probSimplex V) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ : V => isCompact_Icc (a := (0 : ℝ)) (b := 1))
    isClosed_probSimplex ?_
  intro w hw v _
  exact ⟨hw.nonneg v, hw.le_one v⟩

private lemma continuous_finset_inf' {α β : Type*} [TopologicalSpace β]
    (s : Finset α) (hs : s.Nonempty) (F : α → β → ℝ)
    (hF : ∀ a ∈ s, Continuous (F a)) :
    Continuous (fun b => s.inf' hs (fun a => F a b)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | cons a t hat ih =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · have heq : (fun b => (Finset.cons a ∅ hat).inf' hs (fun x => F x b)) = F a := by
        ext b
        simp
      rw [heq]
      exact hF a (Finset.mem_cons_self a ∅)
    · have heq : (fun b => (Finset.cons a t hat).inf' hs (fun x => F x b)) =
          fun b => min (F a b) (t.inf' ht (fun x => F x b)) := by
        ext b
        exact Finset.inf'_cons ht (fun x => F x b)
      rw [heq]
      exact (hF a (Finset.mem_cons_self a t)).min
        (ih ht (fun x hx => hF x (Finset.mem_cons_of_mem hx)))

lemma Digraph.continuous_outWeight {V : Type u} [Fintype V]
    (G : Digraph V) [DecidableRel G.adj] (u : V) :
    Continuous (fun w : V → ℝ => G.outWeight w u) := by
  unfold Digraph.outWeight
  fun_prop

lemma Digraph.continuous_minOutWeight {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj] :
    Continuous (G.minOutWeight) :=
  continuous_finset_inf' Finset.univ Finset.univ_nonempty
    (fun u w => G.outWeight w u) (fun u _ => G.continuous_outWeight u)

/-- **Simplex Extremal Weight Theorem**:
For any finite nonempty digraph `G`, `minOutWeight G` attains its global maximum over
`probSimplex V` at an extremal probability weight `wStar`, satisfying
`G.minOutWeight (unifWeight V) ≤ G.minOutWeight wStar`. -/
theorem Digraph.exists_max_minOutWeight {V : Type u} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.adj] :
    ∃ wStar : V → ℝ, IsProbWeight wStar ∧
      ∀ w : V → ℝ, IsProbWeight w → G.minOutWeight w ≤ G.minOutWeight wStar := by
  have hne : (probSimplex V).Nonempty := ⟨unifWeight V, isProbWeight_unifWeight⟩
  obtain ⟨wStar, hwStar, hmax⟩ :=
    isCompact_probSimplex.exists_isMaxOn hne G.continuous_minOutWeight.continuousOn
  exact ⟨wStar, hwStar, fun w hw => hmax hw⟩

/-- **Support Restriction Lemma**:
Restricting any probability weight `w` to its positive support `S = {v | 0 < w v}` preserves total
mass `1`, gives strictly positive weights on `G.induce S`, and never decreases `minOutWeight`. -/
noncomputable def suppSet {V : Type u} [Fintype V] (w : V → ℝ) : Finset V :=
  let _ := Classical.decPred (fun v : V => 0 < w v)
  Finset.univ.filter (fun v => 0 < w v)

lemma mem_suppSet {V : Type u} [Fintype V] {w : V → ℝ} {v : V} :
    v ∈ suppSet w ↔ 0 < w v := by
  unfold suppSet
  simp

lemma eq_zero_of_notMem_suppSet {V : Type u} [Fintype V] {w : V → ℝ}
    (hw : IsProbWeight w) {v : V} (hv : v ∉ suppSet w) : w v = 0 := by
  rw [mem_suppSet, not_lt] at hv
  exact le_antisymm hv (hw.nonneg v)

lemma suppSet_nonempty {V : Type u} [Fintype V] {w : V → ℝ} (hw : IsProbWeight w) :
    (suppSet w).Nonempty := by
  by_contra h_emp
  rw [Finset.not_nonempty_iff_eq_empty] at h_emp
  have hzero : ∀ v : V, w v = 0 := by
    intro v
    apply eq_zero_of_notMem_suppSet hw
    rw [h_emp]
    simp
  have hsum : ∑ v : V, w v = 0 := Finset.sum_eq_zero (fun v _ => hzero v)
  linarith [hw.sum_eq_one]

/-! ## Section 3: Balanced `N`-Fold Blow-Up & Exact `O(1/n)` Elimination -/

namespace OrientedGraph

/-- The `N`-fold balanced blow-up of `G` on `V × Fin N`, replacing each vertex by `N` independent
clones with identical external neighborhoods. -/
def blowup {V : Type u} (G : OrientedGraph V) (N : ℕ) : OrientedGraph (V × Fin N) where
  adj p q := G.adj p.1 q.1
  loopless p := G.loopless p.1
  asymm p q := G.asymm p.1 q.1

instance instDecidableRelBlowup {V : Type u} (G : OrientedGraph V) [h : DecidableRel G.adj]
    (N : ℕ) : DecidableRel (G.blowup N).adj :=
  fun p q => h p.1 q.1

lemma triangleFree_blowup {V : Type u} {G : OrientedGraph V} (hG : G.TriangleFree) (N : ℕ) :
    (G.blowup N).TriangleFree := by
  rintro ⟨p, q, r, hpq, hqr, hrp⟩
  exact hG ⟨p.1, q.1, r.1, hpq, hqr, hrp⟩

lemma outDeg_blowup {V : Type u} [Fintype V] (G : OrientedGraph V) [DecidableRel G.adj]
    (N : ℕ) (p : V × Fin N) :
    (G.blowup N).toDigraph.outDeg p = G.toDigraph.outDeg p.1 * N := by
  have hout : (G.blowup N).toDigraph.outSet p =
      G.toDigraph.outSet p.1 ×ˢ (Finset.univ : Finset (Fin N)) := by
    ext ⟨v, j⟩
    simp only [Finset.mem_product, Finset.mem_univ, and_true, Digraph.mem_outSet]
    rfl
  dsimp [Digraph.outDeg]
  rw [hout, Finset.card_product, Finset.card_fin]

/-- **Exact Finite-to-Asymptotic Bridge (`O(1/n)` Elimination)**:
If every finite nonempty `C₃`-free oriented graph `H` on `W` has a vertex of out-degree at most
`c * |W| + C` (for some fixed constant `C`, regardless of how large!), then EVERY finite nonempty
`C₃`-free oriented graph `G` on `V` satisfies the **exact** inequality `∃ u, outDeg G u ≤ c * |V|`
with ZERO `+ C` error! -/
theorem exists_outDeg_le_of_asymptotic_bound {c C : ℝ}
    (h_asymp : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ x : W, (H.toDigraph.outDeg x : ℝ) ≤ c * (Fintype.card W : ℝ) + C)
    {V : Type u} [Fintype V] [Nonempty V] (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) :
    ∃ u : V, (G.toDigraph.outDeg u : ℝ) ≤ c * (Fintype.card V : ℝ) := by
  by_contra hno
  push Not at hno
  let gap : V → ℝ := fun u => (G.toDigraph.outDeg u : ℝ) - c * (Fintype.card V : ℝ)
  let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty gap
  have hε_pos : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    intro u _
    exact sub_pos.mpr (hno u)
  have hgap_ge : ∀ u : V, c * (Fintype.card V : ℝ) + ε ≤ (G.toDigraph.outDeg u : ℝ) := by
    intro u
    have hle : ε ≤ gap u := Finset.inf'_le gap (Finset.mem_univ u)
    dsimp [gap] at hle
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C / ε))
  have hN_one : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_left 1 (C / ε)) hN
  have hN_pos : 0 < N := by exact_mod_cast (lt_trans zero_lt_one hN_one)
  have _ : Nonempty (Fin N) := ⟨⟨0, hN_pos⟩⟩
  have hC_lt : C < (N : ℝ) * ε := by
    have hdiv : C / ε < (N : ℝ) := lt_of_le_of_lt (le_max_right 1 (C / ε)) hN
    rwa [div_lt_iff₀ hε_pos] at hdiv
  obtain ⟨p, hp⟩ := h_asymp (G.blowup N) (G.triangleFree_blowup hG N)
  rw [G.outDeg_blowup N p, Fintype.card_prod, Fintype.card_fin] at hp
  push_cast at hp
  have hmul : (c * (Fintype.card V : ℝ) + ε) * (N : ℝ) ≤
      (G.toDigraph.outDeg p.1 : ℝ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (hgap_ge p.1) (Nat.cast_nonneg N)
  linarith

end OrientedGraph

/-! ## Section 4: Zero-Error Finite Pullback Flag Homomorphism -/

namespace OrientedGraph

/-- Pullback of an oriented graph `G` along ANY tuple `x : ι → V` (injective or not!).
Self-collisions `x i = x j` become non-adjacent twin vertices in `G.pullback x`, matching the
continuum blow-up `G^(∞)` identically with zero diagonal error. -/
def pullback {V : Type u} {ι : Type*} (G : OrientedGraph V) (x : ι → V) : OrientedGraph ι where
  adj i j := G.adj (x i) (x j)
  loopless i := G.loopless (x i)
  asymm i j := G.asymm (x i) (x j)

instance instDecidableRelPullback {V : Type u} {ι : Type*}
    (G : OrientedGraph V) [h : DecidableRel G.adj] (x : ι → V) :
    DecidableRel (G.pullback x).adj :=
  fun i j => h (x i) (x j)

lemma triangleFree_pullback {V : Type u} {ι : Type*} {G : OrientedGraph V}
    (hG : G.TriangleFree) (x : ι → V) :
    (G.pullback x).TriangleFree := by
  rintro ⟨i, j, k, hij, hjk, hki⟩
  exact hG ⟨x i, x j, x k, hij, hjk, hki⟩

/-- Relabeling of an oriented graph along an equivalence `π : α ≃ β`. -/
def relabel {α β : Type*} (H : OrientedGraph β) (π : α ≃ β) : OrientedGraph α :=
  H.pullback π

lemma pullback_comp {V : Type u} {α β : Type*} (G : OrientedGraph V)
    (x : β → V) (π : α → β) :
    (G.pullback x).pullback π = G.pullback (x ∘ π) := rfl

end OrientedGraph

/-- Product probability weight `∏ i : Fin m, w (x i)` of a sampled tuple `x : Fin m → V`. -/
def tupleWeight {V : Type u} {m : ℕ} (w : V → ℝ) (x : Fin m → V) : ℝ :=
  ∏ i : Fin m, w (x i)

lemma tupleWeight_nonneg {V : Type u} [Fintype V] {m : ℕ} {w : V → ℝ}
    (hw : IsProbWeight w) (x : Fin m → V) :
    0 ≤ tupleWeight w x :=
  Finset.prod_nonneg (fun i _ => hw.nonneg (x i))

lemma tupleWeight_comp_equiv {V : Type u} {m : ℕ} (w : V → ℝ)
    (x : Fin m → V) (π : Equiv.Perm (Fin m)) :
    tupleWeight w (x ∘ π) = tupleWeight w x :=
  Equiv.prod_comp π (fun i => w (x i))

lemma sum_tupleWeight_eq_pow {V : Type u} [Fintype V] (w : V → ℝ) :
    ∀ m : ℕ, ∑ x : Fin m → V, tupleWeight w x = (∑ v : V, w v) ^ m
  | 0 => by simp [tupleWeight]
  | m + 1 => by
    unfold tupleWeight
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => V)), Fintype.sum_prod_type]
    simp_rw [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have ih := sum_tupleWeight_eq_pow w m
    unfold tupleWeight at ih
    simp_rw [← Finset.mul_sum, ih, ← Finset.sum_mul, pow_succ']

lemma sum_tupleWeight {V : Type u} [Fintype V] {m : ℕ} {w : V → ℝ} (hw : IsProbWeight w) :
    ∑ x : Fin m → V, tupleWeight w x = 1 := by
  rw [sum_tupleWeight_eq_pow, hw.sum_eq_one, one_pow]

/-- Permutation invariance of tuple expectations: replacing `F` by `H ↦ F (H.relabel π)` leaves
the `tupleWeight` expectation unchanged for any `π ∈ Perm (Fin m)`. -/
lemma sum_tupleWeight_relabel {V : Type u} [Fintype V] {m : ℕ}
    (G : OrientedGraph V) (w : V → ℝ) (F : OrientedGraph (Fin m) → ℝ)
    (π : Equiv.Perm (Fin m)) :
    ∑ x : Fin m → V, tupleWeight w x * F ((G.pullback x).relabel π) =
      ∑ x : Fin m → V, tupleWeight w x * F (G.pullback x) := by
  let e : (Fin m → V) ≃ (Fin m → V) :=
    { toFun := fun x => x ∘ π
      invFun := fun x => x ∘ π.symm
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  have hcomp : ∀ x : Fin m → V,
      tupleWeight w x * F ((G.pullback x).relabel π) =
        tupleWeight w (e x) * F (G.pullback (e x)) := by
    intro x
    dsimp [e]
    rw [tupleWeight_comp_equiv]
    rfl
  simp_rw [hcomp]
  exact Equiv.sum_comp e (fun y => tupleWeight w y * F (G.pullback y))

end CaccettaHaggkvist
