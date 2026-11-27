module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.WeightBridge
public import CaccettaHaggkvist.FlagCert
public import CaccettaHaggkvist.CSS
public import CaccettaHaggkvist.CSS56
public import CaccettaHaggkvist.CSS83
public import CaccettaHaggkvist.ExtremalBridge
public import CaccettaHaggkvist.KernelCore
public import CaccettaHaggkvist.VanillaCertBridge

/-!
# Expectation bounds for affine flag terms

This module proves the zero mean of the out-degree term, the lower bound for linear
induction terms, and nonnegativity of the linear CSS terms with coefficients 1 and 5/6.
The unweighted square terms are defined in `VanillaCertBridge`. The conditional-mean
formula for a localized square is proved in `WeightedFlags`.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

/-! ## Section 1: Decoding `graphTritCode` & Verifying `codeHasSinkOrWitness` -/

def tritCodeAdj : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | s + 1, code, a, b =>
    let p3 := Nat.pow 3 s
    let row := Nat.mod code p3
    let sub := Nat.div code p3
    cond (natLtBool a s)
      (cond (natLtBool b s) (tritCodeAdj s sub a b)
        (cond (Nat.beq b s) (Nat.beq (tritAt row a) 1) false))
      (cond (Nat.beq a s)
        (cond (natLtBool b s) (Nat.beq (tritAt row b) 2) false)
        false)

lemma adj_iff_tritCodeAdj : ∀ {r : ℕ} (K : OrientedGraph (Fin r)) (x y : Fin r),
    K.adj x y ↔ tritCodeAdj r (graphTritCode K) x.1 y.1 = true
  | 0, _, x, _ => x.elim0
  | s + 1, K, x, y => by
    have hp3_pos : 0 < 3 ^ s := Nat.pow_pos (by omega)
    have hlt := packTrits_lt (edgeTritG K)
    have hmod : Nat.mod (packTrits (edgeTritG K) + 3 ^ s * graphTritCode (K.pullback Fin.castSucc))
        (Nat.pow 3 s) = packTrits (edgeTritG K) := by
      change (packTrits (edgeTritG K) + 3 ^ s * graphTritCode (K.pullback Fin.castSucc)) % (3 ^ s) = _
      rw [mul_comm (3 ^ s), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have hdiv : Nat.div (packTrits (edgeTritG K) + 3 ^ s * graphTritCode (K.pullback Fin.castSucc))
        (Nat.pow 3 s) = graphTritCode (K.pullback Fin.castSucc) := by
      change (packTrits (edgeTritG K) + 3 ^ s * graphTritCode (K.pullback Fin.castSucc)) / (3 ^ s) = _
      rw [mul_comm (3 ^ s), Nat.add_mul_div_right _ _ hp3_pos, Nat.div_eq_of_lt hlt, zero_add]
    change K.adj x y ↔
      tritCodeAdj (s + 1) (packTrits (edgeTritG K) + 3 ^ s * graphTritCode (K.pullback Fin.castSucc)) x.1 y.1 = true
    unfold tritCodeAdj
    dsimp only
    rw [hmod, hdiv]
    have hbs : Nat.beq s s = true := Nat.beq_eq.mpr rfl
    have hns : natLtBool s s = false := natLtBool_eq_false_iff.mpr (lt_irrefl s)
    refine Fin.lastCases ?_ ?_ x
    · refine Fin.lastCases ?_ ?_ y
      · simp only [Fin.val_last, hns, hbs, Bool.cond_false, Bool.cond_true]
        exact ⟨fun h => (K.loopless _ h).elim, fun h => Bool.noConfusion h⟩
      · intro j
        have hj : natLtBool j.1 s = true := natLtBool_eq_true_iff.mpr j.isLt
        simp only [Fin.val_last, Fin.val_castSucc, hns, hbs, hj, Bool.cond_false, Bool.cond_true,
          Nat.beq_eq, tritAt_packTrits, edgeTritG]
        by_cases h1 : K.adj j.castSucc (Fin.last s)
        · have h2 : ¬ K.adj (Fin.last s) j.castSucc := K.asymm _ _ h1
          simp [h1, h2]
        · by_cases h2 : K.adj (Fin.last s) j.castSucc <;> simp [h1, h2]
    · intro i
      have hi : natLtBool i.1 s = true := natLtBool_eq_true_iff.mpr i.isLt
      refine Fin.lastCases ?_ ?_ y
      · simp only [Fin.val_castSucc, Fin.val_last, hi, hns, hbs, Bool.cond_true, Bool.cond_false,
          Nat.beq_eq, tritAt_packTrits, edgeTritG]
        by_cases h1 : K.adj i.castSucc (Fin.last s)
        · simp [h1]
        · by_cases h2 : K.adj (Fin.last s) i.castSucc <;> simp [h1, h2]
      · intro j
        have hj : natLtBool j.1 s = true := natLtBool_eq_true_iff.mpr j.isLt
        simp only [Fin.val_castSucc, hi, hj, Bool.cond_true]
        exact adj_iff_tritCodeAdj (K.pullback Fin.castSucc) i j

def codeHasSink (k_orig r code : ℕ) : Bool :=
  !(allBelow k_orig (fun s =>
    !(allBelow k_orig (fun i =>
      (Nat.beq i s) || tritCodeAdj r code i s))))

def codeHasWitness (k_orig r code : ℕ) : Bool :=
  (natLtBool k_orig r) &&
  allBelow k_orig (fun i => tritCodeAdj r code i k_orig)

def codeHasSinkOrWitness (k_orig r code : ℕ) : Bool :=
  codeHasSink k_orig r code || codeHasWitness k_orig r code

lemma of_codeHasSinkOrWitness {k_orig r : ℕ} (hk : k_orig ≤ r) (hk_bdd : k_orig ≤ 2 ^ 17)
    (K : OrientedGraph (Fin r))
    (h : codeHasSinkOrWitness k_orig r (graphTritCode K) = true) :
    (∃ s : Fin k_orig, ∀ i : Fin k_orig, i ≠ s → K.adj ⟨i.1, by omega⟩ ⟨s.1, by omega⟩) ∨
    (∃ hlt : k_orig < r, ∀ i : Fin k_orig, K.adj ⟨i.1, by omega⟩ ⟨k_orig, hlt⟩) := by
  unfold codeHasSinkOrWitness at h
  simp only [Bool.or_eq_true] at h
  rcases h with hsink | hwit
  · left
    by_contra hno
    push Not at hno
    unfold codeHasSink at hsink
    have hall : allBelow k_orig (fun s =>
        !(allBelow k_orig (fun i => (Nat.beq i s) || tritCodeAdj r (graphTritCode K) i s))) = true := by
      refine allBelow_eq_true_of_forall hk_bdd fun s hs => ?_
      obtain ⟨i, hne, hnadj⟩ := hno ⟨s, hs⟩
      have hfalse : allBelow k_orig (fun i => (Nat.beq i s) || tritCodeAdj r (graphTritCode K) i s) =
          false := by
        by_contra htr
        simp only [Bool.not_eq_false] at htr
        have hi := of_allBelow htr i.isLt
        simp only [Bool.or_eq_true, Nat.beq_eq] at hi
        rcases hi with heq | hadj
        · exact hne (Fin.ext heq)
        · exact hnadj ((adj_iff_tritCodeAdj K ⟨i.1, by omega⟩ ⟨s, by omega⟩).mpr hadj)
      simp [hfalse]
    rw [hall] at hsink
    cases hsink
  · right
    unfold codeHasWitness at hwit
    simp only [Bool.and_eq_true, natLtBool_eq_true_iff] at hwit
    refine ⟨hwit.1, fun i => ?_⟩
    exact (adj_iff_tritCodeAdj K ⟨i.1, by omega⟩ ⟨k_orig, hwit.1⟩).mpr (of_allBelow hwit.2 i.isLt)

/-! ## Section 2: Class 1 (`degAffineU`, `degAffineV`) Exact Zero Expectation on `G₀` -/

noncomputable def degAffineU {r : ℕ} (g : OrientedGraph (Fin (r + 1)) → ℝ)
    (K : OrientedGraph (Fin (r + 2))) : ℝ :=
  g (K.pullback embSkipOne) * (@ite ℝ (K.adj 0 1) (Classical.propDecidable _) 1 0)

noncomputable def degAffineV {r : ℕ} (g : OrientedGraph (Fin (r + 1)) → ℝ)
    (K : OrientedGraph (Fin (r + 2))) : ℝ :=
  - g (K.pullback embSkipOne)

theorem expect_degAffine_eq_zero {W : Type*} [Fintype W] {r : ℕ}
    (G₀ : OrientedGraph W) [DecidableRel G₀.adj]
    {w : W → ℝ} (hw : IsProbWeight w) {c₀ : ℝ}
    (hreg : ∀ u : W, G₀.toDigraph.outWeight w u = c₀)
    (g : OrientedGraph (Fin (r + 1)) → ℝ) :
    ∑ x : Fin (r + 2) → W,
      tupleWeight w x *
        (degAffineU g (G₀.pullback x) + c₀ * degAffineV g (G₀.pullback x)) = 0 := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 2) => W)), Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => W)), Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hterm : ∀ v : W,
      tupleWeight w ((Fin.consEquiv (fun _ : Fin (r + 2) => W))
        (u, (Fin.consEquiv (fun _ : Fin (r + 1) => W)) (v, y))) *
        (degAffineU g (G₀.pullback
          ((Fin.consEquiv (fun _ : Fin (r + 2) => W))
            (u, (Fin.consEquiv (fun _ : Fin (r + 1) => W)) (v, y)))) +
        c₀ * degAffineV g (G₀.pullback
          ((Fin.consEquiv (fun _ : Fin (r + 2) => W))
            (u, (Fin.consEquiv (fun _ : Fin (r + 1) => W)) (v, y))))) =
      w u * tupleWeight w y * g (G₀.pullback (Fin.cons u y)) *
        (w v * ((if G₀.adj u v then (1 : ℝ) else 0) - c₀)) := by
    intro v
    simp only [Fin.consEquiv_apply]
    have hpull : (G₀.pullback (Fin.cons u (Fin.cons v y))).pullback embSkipOne =
        G₀.pullback (Fin.cons u y) := by
      rw [OrientedGraph.pullback_comp]
      congr 1; ext a; cases a using Fin.cases <;> rfl
    have hadj :
        (@ite ℝ ((G₀.pullback (Fin.cons u (Fin.cons v y))).adj 0 1)
          (Classical.propDecidable _) (1 : ℝ) 0) =
        (if G₀.adj u v then (1 : ℝ) else 0) := by
      change (@ite ℝ (G₀.adj u v) (Classical.propDecidable _) (1 : ℝ) 0) = _
      by_cases huv : G₀.adj u v <;> simp [huv]
    have htw : tupleWeight w (Fin.cons u (Fin.cons v y)) =
        w u * (w v * tupleWeight w y) := by
      unfold tupleWeight
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp_rw [Fin.cons_succ]
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp_rw [Fin.cons_succ]
    unfold degAffineU degAffineV
    rw [hpull, hadj, htw]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  have hv_sum : ∑ v : W, w v * ((if G₀.adj u v then (1 : ℝ) else 0) - c₀) = 0 := by
    have hsplit : ∑ v : W, w v * ((if G₀.adj u v then (1 : ℝ) else 0) - c₀) =
        (∑ v : W, if G₀.adj u v then w v else 0) - c₀ * (∑ v : W, w v) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
    have hfilter : (∑ v : W, if G₀.adj u v then w v else 0) = G₀.toDigraph.outWeight w u := by
      unfold Digraph.outWeight Digraph.outSet; rw [Finset.sum_filter]
    rw [hsplit, hfilter, hreg u, hw.sum_eq_one, mul_one, sub_self]
  rw [hv_sum, mul_zero]

/-! ## Section 3: Class 3 Linear Generalized Induction (`≥ -M_bdd * ε`) -/

def allInPred {r : ℕ} (k_orig : ℕ) (hk : k_orig ≤ r) (K : OrientedGraph (Fin (r + 1))) : Prop :=
  ∀ i : Fin k_orig, K.adj ⟨i.1, by omega⟩ (Fin.last r)

def srcStarPred {r : ℕ} (k_orig : ℕ) (hk : k_orig ≤ r) (K : OrientedGraph (Fin (r + 1))) : Prop :=
  (∀ i : Fin k_orig, ¬ K.adj (Fin.last r) ⟨i.1, by omega⟩) ∧ ¬ allInPred k_orig hk K

noncomputable def linIndU {r : ℕ} (k_orig : ℕ) (hk : k_orig ≤ r) (indTree : NTree)
    (K : OrientedGraph (Fin (r + 1))) : ℝ :=
  (indTree.get (graphTritCode (K.pullback Fin.castSucc)) : ℝ) *
    (@ite ℝ (srcStarPred k_orig hk K) (Classical.propDecidable _) 1 0)

noncomputable def linIndV {r : ℕ} (k_orig : ℕ) (hk : k_orig ≤ r) (indTree : NTree)
    (K : OrientedGraph (Fin (r + 1))) : ℝ :=
  (indTree.get (graphTritCode (K.pullback Fin.castSucc)) : ℝ) *
    ((@ite ℝ (allInPred k_orig hk K) (Classical.propDecidable _) 1 0) - 1)

def checkIndTree (k_orig r m_bdd : ℕ) (indTree : NTree) : Bool :=
  allBelow (Nat.pow 3 (Nat.div (Nat.mul r (Nat.sub r 1)) 2)) (fun c =>
    let v := indTree.get c
    (Nat.ble v m_bdd) && ((Nat.beq v 0) || codeHasSinkOrWitness k_orig r c))

private def equivFin1 (α : Type*) : α ≃ (Fin 1 → α) where
  toFun x _ := x
  invFun z := z 0
  left_inv _ := rfl
  right_inv z := by ext i; rw [Subsingleton.elim i 0]

private lemma tupleWeight_unif_fin1 {n : ℕ} (x : Fin n) :
    tupleWeight (unifWeight (Fin n)) (equivFin1 (Fin n) x) = 1 / (n : ℝ) := by
  unfold tupleWeight unifWeight
  simp [Fintype.card_fin]

theorem expect_linInd_ge {n r k_orig m_bdd : ℕ} (hn : 0 < n)
    (hk : k_orig ≤ r) (hk_bdd : k_orig ≤ 2 ^ 17)
    {indTree : NTree} (hchk : checkIndTree k_orig r m_bdd indTree = true)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ u : Fin n, G₀.toDigraph.outWeight (unifWeight (Fin n)) u = c₀)
    (hhered : ∀ U : Finset (Fin n), U.Nonempty →
      ∃ w ∈ U, ((U ∩ G₀.toDigraph.outSet w).card : ℝ) ≤ (c₀ + ε) * (U.card : ℝ)) :
    -(m_bdd : ℝ) * ε ≤ ∑ z : Fin (r + 1) → Fin n,
      tupleWeight (unifWeight (Fin n)) z *
        (linIndU k_orig hk indTree (G₀.pullback z) +
          c₀ * linIndV k_orig hk indTree (G₀.pullback z)) := by
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hreg_deg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ) := by
    intro w
    have hw := hreg w
    rw [Digraph.outWeight_unifWeight, Fintype.card_fin, div_eq_iff hn_pos.ne'] at hw
    exact hw
  obtain ⟨e1, he1⟩ := appendTuple_equiv (W := Fin n) (a := r) (b := 1)
  rw [← Equiv.sum_comp e1, Fintype.sum_prod_type]
  simp_rw [he1]
  have hw_unif : IsProbWeight (unifWeight (Fin n)) := isProbWeight_unifWeight
  have hper_y : ∀ y ∈ (Finset.univ : Finset (Fin r → Fin n)),
      tupleWeight (unifWeight (Fin n)) y * (-(m_bdd : ℝ) * ε) ≤
        ∑ z1 : Fin 1 → Fin n,
          tupleWeight (unifWeight (Fin n)) (appendTuple y z1) *
            (linIndU k_orig hk indTree (G₀.pullback (appendTuple y z1)) +
              c₀ * linIndV k_orig hk indTree (G₀.pullback (appendTuple y z1))) := by
    intro y _
    rw [← Equiv.sum_comp (equivFin1 (Fin n))]
    let K' := G₀.pullback y
    let mv := indTree.get (graphTritCode K')
    have hc_lt : graphTritCode K' < 3 ^ (r * (r - 1) / 2) := graphTritCode_lt K'
    have hcell := of_allBelow hchk hc_lt
    simp only [Bool.and_eq_true, Nat.ble_eq] at hcell
    have hmv_le : (mv : ℝ) ≤ (m_bdd : ℝ) := by exact_mod_cast hcell.1
    let v_orig : Fin k_orig → Fin n := fun i => y ⟨i.1, by omega⟩
    have hterm_x : ∀ x : Fin n,
        tupleWeight (unifWeight (Fin n)) (appendTuple y (equivFin1 (Fin n) x)) *
          (linIndU k_orig hk indTree (G₀.pullback (appendTuple y (equivFin1 (Fin n) x))) +
            c₀ * linIndV k_orig hk indTree (G₀.pullback (appendTuple y (equivFin1 (Fin n) x)))) =
        tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) * (1 / (n : ℝ)) *
          ((if x ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) +
            c₀ * ((if x ∈ commonOutSet G₀ v_orig then (1 : ℝ) else 0) - 1)) := by
      intro x
      rw [tupleWeight_appendTuple, tupleWeight_unif_fin1]
      have hpull : (G₀.pullback (appendTuple y (equivFin1 (Fin n) x))).pullback Fin.castSucc = K' := by
        rw [OrientedGraph.pullback_comp]
        congr 1; ext j; simp [appendTuple, j.isLt]
      have hall_iff : allInPred k_orig hk (G₀.pullback (appendTuple y (equivFin1 (Fin n) x))) ↔
          x ∈ commonOutSet G₀ v_orig := by
        simp only [allInPred, commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine forall_congr' fun i => ?_
        have hi : i.1 < r := by omega
        change G₀.adj (appendTuple y (equivFin1 (Fin n) x) ⟨i.1, _⟩)
          (appendTuple y (equivFin1 (Fin n) x) (Fin.last r)) ↔ G₀.adj (v_orig i) x
        simp [appendTuple, hi, equivFin1, v_orig]
      have hsrc_iff : srcStarPred k_orig hk (G₀.pullback (appendTuple y (equivFin1 (Fin n) x))) ↔
          x ∈ srcStarSet G₀ v_orig := by
        simp only [srcStarPred, hall_iff, srcStarSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine and_congr ?_ (not_congr ?_)
        · refine forall_congr' fun i => not_congr ?_
          have hi : i.1 < r := by omega
          change G₀.adj (appendTuple y (equivFin1 (Fin n) x) (Fin.last r))
            (appendTuple y (equivFin1 (Fin n) x) ⟨i.1, _⟩) ↔ G₀.adj x (v_orig i)
          simp [appendTuple, hi, equivFin1, v_orig]
        · simp [commonOutSet]
      unfold linIndU linIndV
      rw [hpull]
      have hi1 : (@ite ℝ (srcStarPred k_orig hk (G₀.pullback (appendTuple y (equivFin1 (Fin n) x))))
          (Classical.propDecidable _) 1 0) = if x ∈ srcStarSet G₀ v_orig then 1 else 0 := by
        by_cases hs : x ∈ srcStarSet G₀ v_orig
        · simp only [hs, ↓reduceIte, ite_eq_left_iff]; exact fun h => (h (hsrc_iff.mpr hs)).elim
        · simp only [hs, ↓reduceIte, ite_eq_right_iff]; exact fun h => (hs (hsrc_iff.mp h)).elim
      have hi2 : (@ite ℝ (allInPred k_orig hk (G₀.pullback (appendTuple y (equivFin1 (Fin n) x))))
          (Classical.propDecidable _) 1 0) = if x ∈ commonOutSet G₀ v_orig then 1 else 0 := by
        by_cases ha : x ∈ commonOutSet G₀ v_orig
        · simp only [ha, ↓reduceIte, ite_eq_left_iff]; exact fun h => (h (hall_iff.mpr ha)).elim
        · simp only [ha, ↓reduceIte, ite_eq_right_iff]; exact fun h => (ha (hall_iff.mp h)).elim
      rw [hi1, hi2]
      dsimp only [mv]
      ring
    simp_rw [hterm_x, ← Finset.mul_sum]
    have hsum_x : (1 / (n : ℝ)) * ∑ x : Fin n,
        ((if x ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) +
          c₀ * ((if x ∈ commonOutSet G₀ v_orig then (1 : ℝ) else 0) - 1)) =
        ((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ) +
          c₀ * (((commonOutSet G₀ v_orig).card : ℝ) / (n : ℝ)) - c₀ := by
      have hs1 : ∑ x : Fin n, (if x ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) =
          ((srcStarSet G₀ v_orig).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, mul_one]
      have hs2 : ∑ x : Fin n, ((if x ∈ commonOutSet G₀ v_orig then (1 : ℝ) else 0) - 1) =
          ((commonOutSet G₀ v_orig).card : ℝ) - (n : ℝ) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.univ_inter, Finset.sum_const, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs1, hs2]
      field_simp [hn_pos.ne']
      ring
    have hrew : tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) * (1 / (n : ℝ)) *
        (∑ x : Fin n, ((if x ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) +
          c₀ * ((if x ∈ commonOutSet G₀ v_orig then (1 : ℝ) else 0) - 1))) =
        tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) *
          (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ) +
            c₀ * (((commonOutSet G₀ v_orig).card : ℝ) / (n : ℝ)) - c₀) := by
      rw [← hsum_x]; ring
    rw [hrew]
    have htw_nn : 0 ≤ tupleWeight (unifWeight (Fin n)) y := tupleWeight_nonneg hw_unif y
    have hm_nn : (0 : ℝ) ≤ (m_bdd : ℝ) := Nat.cast_nonneg m_bdd
    by_cases hmv0 : mv = 0
    · rw [hmv0]; simp only [Nat.cast_zero, mul_zero, zero_mul]
      have hme : 0 ≤ (m_bdd : ℝ) * ε := mul_nonneg hm_nn hε
      nlinarith
    · have hb0 : Nat.beq mv 0 = false := by
        cases hq : Nat.beq mv 0
        · rfl
        · exact (hmv0 (Nat.beq_eq.mp hq)).elim
      have hsw : codeHasSinkOrWitness k_orig r (graphTritCode K') = true := by
        simpa [mv, hb0] using hcell.2
      have hineq : -ε ≤ ((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ) +
          c₀ * (((commonOutSet G₀ v_orig).card : ℝ) / (n : ℝ)) - c₀ := by
        rcases of_codeHasSinkOrWitness hk hk_bdd K' hsw with ⟨s, hs⟩ | ⟨hlt, hw⟩
        · exact ind_ineq_of_universal_sink hn G₀ hG₀ hε hreg_deg hhered v_orig s
            (fun i hi => hs i hi)
        · refine ind_ineq_of_commonOut_nonempty hn G₀ hG₀ hε hreg_deg hhered v_orig
            ⟨y ⟨k_orig, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hw i⟩⟩
      have hmv_nn : (0 : ℝ) ≤ (mv : ℝ) := Nat.cast_nonneg mv
      have h1 : tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) * (-ε) ≤
          tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) *
            (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ) +
              c₀ * (((commonOutSet G₀ v_orig).card : ℝ) / (n : ℝ)) - c₀) :=
        mul_le_mul_of_nonneg_left hineq (mul_nonneg htw_nn hmv_nn)
      have h2 : tupleWeight (unifWeight (Fin n)) y * (-(m_bdd : ℝ) * ε) ≤
          tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) * (-ε) := by
        have hdiff : 0 ≤ ((m_bdd : ℝ) - (mv : ℝ)) * ε := mul_nonneg (by linarith) hε
        have hmul : 0 ≤ tupleWeight (unifWeight (Fin n)) y * (((m_bdd : ℝ) - (mv : ℝ)) * ε) :=
          mul_nonneg htw_nn hdiff
        linarith
      exact le_trans h2 h1
  calc -(m_bdd : ℝ) * ε
      = (∑ y : Fin r → Fin n, tupleWeight (unifWeight (Fin n)) y) * (-(m_bdd : ℝ) * ε) := by
          rw [sum_tupleWeight hw_unif, one_mul]
    _ = ∑ y : Fin r → Fin n, tupleWeight (unifWeight (Fin n)) y * (-(m_bdd : ℝ) * ε) :=
          Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum hper_y

/-! ## Section 4: Class 4 Linear Pointwise CSS (`α = 1` AND `α = 5/6`, Exact `≥ 0`!) -/

def embInit2 {r : ℕ} (j : Fin r) : Fin (r + 2) :=
  ⟨j.1, by omega⟩

def chiPred2 {r : ℕ} (k_orig : ℕ) (hk : k_orig ≤ r) (K : OrientedGraph (Fin (r + 2))) : Prop :=
  let p1 : Fin (r + 2) := ⟨r, by omega⟩
  let p2 : Fin (r + 2) := ⟨r + 1, by omega⟩
  (∀ i : Fin k_orig, K.adj ⟨i.1, by omega⟩ p1) ∧
  (∀ i : Fin k_orig, K.adj ⟨i.1, by omega⟩ p2) ∧
  ¬ K.adj p1 p2 ∧ ¬ K.adj p2 p1

def srcStarPred2 {r : ℕ} (k_orig : ℕ) (hk : k_orig ≤ r) (K : OrientedGraph (Fin (r + 2))) : Prop :=
  let p1 : Fin (r + 2) := ⟨r, by omega⟩
  (∀ i : Fin k_orig, ¬ K.adj p1 ⟨i.1, by omega⟩) ∧
  ¬ (∀ i : Fin k_orig, K.adj ⟨i.1, by omega⟩ p1)

/-- Integer-scaled (`× 6 * rd²` when `isTier2 = true`, `× rd²` when `isTier2 = false`) CSS functional:
- Tier 1 (`α = 1`, `a_num = 1, a_den = 1`): `rd² * chi + 2*rn*rd * s* + rn² - c₀ * (2*rn*rd)`
- Tier 2 (`α = 5/6`, `a_num = 5, a_den = 6`): `5*rd² * chi + 12*rn*rd * s* + 6*rn² - c₀ * (12*rn*rd)` -/
noncomputable def linCssU {r : ℕ} (isTier2 : Bool) (k_orig : ℕ) (hk : k_orig ≤ r)
    (rn rd : ℕ) (cssTree : NTree) (K : OrientedGraph (Fin (r + 2))) : ℝ :=
  let a_num : ℝ := if isTier2 then 5 else 1
  let a_den : ℝ := if isTier2 then 6 else 1
  (cssTree.get (graphTritCode (K.pullback embInit2)) : ℝ) *
    (a_num * (rd : ℝ) ^ 2 * (@ite ℝ (chiPred2 k_orig hk K) (Classical.propDecidable _) 1 0) +
      2 * a_den * (rn : ℝ) * (rd : ℝ) *
        (@ite ℝ (srcStarPred2 k_orig hk K) (Classical.propDecidable _) 1 0) +
      a_den * (rn : ℝ) ^ 2)

noncomputable def linCssV {r : ℕ} (isTier2 : Bool) (k_orig : ℕ) (_hk : k_orig ≤ r)
    (rn rd : ℕ) (cssTree : NTree) (K : OrientedGraph (Fin (r + 2))) : ℝ :=
  -(cssTree.get (graphTritCode (K.pullback embInit2)) : ℝ) *
    (2 * (if isTier2 then (6 : ℝ) else 1) * (rn : ℝ) * (rd : ℝ))

def checkCssTree (k_orig r : ℕ) (cssTree : NTree) : Bool :=
  allBelow (Nat.pow 3 (Nat.div (Nat.mul r (Nat.sub r 1)) 2)) (fun c =>
    (Nat.beq (cssTree.get c) 0) || codeHasSinkOrWitness k_orig r c)

private def equivFin2 (α : Type*) : α × α ≃ (Fin 2 → α) where
  toFun p := Fin.cases p.1 (fun _ => p.2)
  invFun z := (z 0, z 1)
  left_inv _ := rfl
  right_inv z := by
    ext i
    fin_cases i <;> rfl

private lemma tupleWeight_unif_fin2 {n : ℕ} (p : Fin n × Fin n) :
    tupleWeight (unifWeight (Fin n)) (equivFin2 (Fin n) p) = 1 / ((n : ℝ) ^ 2) := by
  unfold tupleWeight unifWeight
  rw [Fin.prod_univ_two]
  simp [Fintype.card_fin, sq]

theorem expect_linCss_nonneg {n r k_orig rn rd : ℕ} (hn : 0 < n) (hrd : 0 < rd)
    (isTier2 : Bool) (hk : k_orig ≤ r) (hk_bdd : k_orig ≤ 2 ^ 17)
    {cssTree : NTree} (hchk : checkCssTree k_orig r cssTree = true)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ : ℝ}
    (hreg : ∀ u : Fin n, G₀.toDigraph.outWeight (unifWeight (Fin n)) u = c₀) :
    0 ≤ ∑ z : Fin (r + 2) → Fin n,
      tupleWeight (unifWeight (Fin n)) z *
        (linCssU isTier2 k_orig hk rn rd cssTree (G₀.pullback z) +
          c₀ * linCssV isTier2 k_orig hk rn rd cssTree (G₀.pullback z)) := by
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrd_pos : (0 : ℝ) < (rd : ℝ) := Nat.cast_pos.mpr hrd
  have hreg_deg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ) := by
    intro w
    have hw := hreg w
    rw [Digraph.outWeight_unifWeight, Fintype.card_fin, div_eq_iff hn_pos.ne'] at hw
    exact hw
  obtain ⟨e1, he1⟩ := appendTuple_equiv (W := Fin n) (a := r) (b := 2)
  rw [← Equiv.sum_comp e1, Fintype.sum_prod_type]
  simp_rw [he1]
  have hw_unif : IsProbWeight (unifWeight (Fin n)) := isProbWeight_unifWeight
  refine Finset.sum_nonneg fun y _ => ?_
  rw [← Equiv.sum_comp (equivFin2 (Fin n))]
  let K' := G₀.pullback y
  let mv := cssTree.get (graphTritCode K')
  have hc_lt : graphTritCode K' < 3 ^ (r * (r - 1) / 2) := graphTritCode_lt K'
  have hcell := of_allBelow hchk hc_lt
  let v_orig : Fin k_orig → Fin n := fun i => y ⟨i.1, by omega⟩
  let a_num : ℝ := if isTier2 then 5 else 1
  let a_den : ℝ := if isTier2 then 6 else 1
  have hterm_p : ∀ p : Fin n × Fin n,
      tupleWeight (unifWeight (Fin n)) (appendTuple y (equivFin2 (Fin n) p)) *
        (linCssU isTier2 k_orig hk rn rd cssTree (G₀.pullback (appendTuple y (equivFin2 (Fin n) p))) +
          c₀ * linCssV isTier2 k_orig hk rn rd cssTree (G₀.pullback (appendTuple y (equivFin2 (Fin n) p)))) =
      tupleWeight (unifWeight (Fin n)) y * (mv : ℝ) * (1 / ((n : ℝ) ^ 2)) *
        (a_num * (rd : ℝ) ^ 2 * (if p ∈ chiPairSet G₀ v_orig then (1 : ℝ) else 0) +
          2 * a_den * (rn : ℝ) * (rd : ℝ) * (if p.1 ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) +
          (a_den * (rn : ℝ) ^ 2 - c₀ * (2 * a_den * (rn : ℝ) * (rd : ℝ)))) := by
    intro p
    rw [tupleWeight_appendTuple, tupleWeight_unif_fin2]
    have hpull : (G₀.pullback (appendTuple y (equivFin2 (Fin n) p))).pullback embInit2 = K' := by
      rw [OrientedGraph.pullback_comp]
      congr 1; ext j; simp [embInit2, appendTuple, j.isLt]
    have hp1 : appendTuple y (equivFin2 (Fin n) p) ⟨r, by omega⟩ = p.1 := by
      simp [appendTuple]
      rfl
    have hp2 : appendTuple y (equivFin2 (Fin n) p) ⟨r + 1, by omega⟩ = p.2 := by
      have hnr : ¬ (r + 1 < r) := by omega
      have hsub : r + 1 - r = 1 := by omega
      simp [appendTuple, hnr, hsub]
      rfl
    have hchi_iff : chiPred2 k_orig hk (G₀.pullback (appendTuple y (equivFin2 (Fin n) p))) ↔
        p ∈ chiPairSet G₀ v_orig := by
      simp only [chiPred2, chiPairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
      · refine forall_congr' fun i => ?_
        have hi : i.1 < r := by omega
        change G₀.adj (appendTuple y (equivFin2 (Fin n) p) ⟨i.1, _⟩)
          (appendTuple y (equivFin2 (Fin n) p) ⟨r, _⟩) ↔ G₀.adj (v_orig i) p.1
        rw [hp1]; simp [appendTuple, hi, v_orig]
      · refine forall_congr' fun i => ?_
        have hi : i.1 < r := by omega
        change G₀.adj (appendTuple y (equivFin2 (Fin n) p) ⟨i.1, _⟩)
          (appendTuple y (equivFin2 (Fin n) p) ⟨r + 1, _⟩) ↔ G₀.adj (v_orig i) p.2
        rw [hp2]; simp [appendTuple, hi, v_orig]
      · refine not_congr ?_
        change G₀.adj (appendTuple y _ ⟨r, _⟩) (appendTuple y _ ⟨r + 1, _⟩) ↔ G₀.adj p.1 p.2
        rw [hp1, hp2]
      · refine not_congr ?_
        change G₀.adj (appendTuple y _ ⟨r + 1, _⟩) (appendTuple y _ ⟨r, _⟩) ↔ G₀.adj p.2 p.1
        rw [hp1, hp2]
    have hsrc_iff : srcStarPred2 k_orig hk (G₀.pullback (appendTuple y (equivFin2 (Fin n) p))) ↔
        p.1 ∈ srcStarSet G₀ v_orig := by
      simp only [srcStarPred2, srcStarSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr ?_ (not_congr ?_)
      · refine forall_congr' fun i => not_congr ?_
        have hi : i.1 < r := by omega
        change G₀.adj (appendTuple y _ ⟨r, _⟩) (appendTuple y _ ⟨i.1, _⟩) ↔ G₀.adj p.1 (v_orig i)
        rw [hp1]; simp [appendTuple, hi, v_orig]
      · refine forall_congr' fun i => ?_
        have hi : i.1 < r := by omega
        change G₀.adj (appendTuple y _ ⟨i.1, _⟩) (appendTuple y _ ⟨r, _⟩) ↔ G₀.adj (v_orig i) p.1
        rw [hp1]; simp [appendTuple, hi, v_orig]
    unfold linCssU linCssV
    rw [hpull]
    have hi1 : (@ite ℝ (chiPred2 k_orig hk (G₀.pullback (appendTuple y (equivFin2 (Fin n) p))))
        (Classical.propDecidable _) 1 0) = if p ∈ chiPairSet G₀ v_orig then 1 else 0 := by
      by_cases hc : p ∈ chiPairSet G₀ v_orig
      · simp only [hc, ↓reduceIte, ite_eq_left_iff]; exact fun h => (h (hchi_iff.mpr hc)).elim
      · simp only [hc, ↓reduceIte, ite_eq_right_iff]; exact fun h => (hc (hchi_iff.mp h)).elim
    have hi2 : (@ite ℝ (srcStarPred2 k_orig hk (G₀.pullback (appendTuple y (equivFin2 (Fin n) p))))
        (Classical.propDecidable _) 1 0) = if p.1 ∈ srcStarSet G₀ v_orig then 1 else 0 := by
      by_cases hs : p.1 ∈ srcStarSet G₀ v_orig
      · simp only [hs, ↓reduceIte, ite_eq_left_iff]; exact fun h => (h (hsrc_iff.mpr hs)).elim
      · simp only [hs, ↓reduceIte, ite_eq_right_iff]; exact fun h => (hs (hsrc_iff.mp h)).elim
    rw [hi1, hi2]
    dsimp only [mv, a_num, a_den]
    ring
  simp_rw [hterm_p, ← Finset.mul_sum]
  by_cases hmv0 : mv = 0
  · rw [hmv0]; simp
  · have hb0 : Nat.beq mv 0 = false := by
      cases hq : Nat.beq mv 0
      · rfl
      · exact (hmv0 (Nat.beq_eq.mp hq)).elim
    have hsw : codeHasSinkOrWitness k_orig r (graphTritCode K') = true := by
      simpa [mv, hb0] using hcell
    have hs1 : ∑ p : Fin n × Fin n, (if p ∈ chiPairSet G₀ v_orig then (1 : ℝ) else 0) =
        ((chiPairSet G₀ v_orig).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hs2 : ∑ p : Fin n × Fin n, (if p.1 ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) =
        (n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ) := by
      rw [Fintype.sum_prod_type]
      have hin : ∀ x₁ : Fin n, ∑ _x₂ : Fin n, (if x₁ ∈ srcStarSet G₀ v_orig then (1 : ℝ) else 0) =
          (n : ℝ) * (if x₁ ∈ srcStarSet G₀ v_orig then 1 else 0) :=
        fun x₁ => by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [hin, ← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hs3 : ∑ _p : Fin n × Fin n,
        (a_den * (rn : ℝ) ^ 2 - c₀ * (2 * a_den * (rn : ℝ) * (rd : ℝ))) =
        (n : ℝ) ^ 2 * (a_den * (rn : ℝ) ^ 2 - c₀ * (2 * a_den * (rn : ℝ) * (rd : ℝ))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]; push_cast; ring
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hs1, hs2, hs3]
    let r_val : ℝ := (rn : ℝ) / (rd : ℝ)
    have hr_nn : 0 ≤ r_val := div_nonneg (Nat.cast_nonneg _) hrd_pos.le
    have htw_nn : 0 ≤ tupleWeight (unifWeight (Fin n)) y := tupleWeight_nonneg hw_unif y
    have hmv_nn : (0 : ℝ) ≤ (mv : ℝ) := Nat.cast_nonneg mv
    refine mul_nonneg (mul_nonneg (mul_nonneg htw_nn hmv_nn) (by positivity)) ?_
    cases isTier2
    · -- Tier 1 (α = 1): a_num = 1, a_den = 1
      have hcss : 0 ≤ ((chiPairSet G₀ v_orig).card : ℝ) / ((n : ℝ) ^ 2) +
          2 * r_val * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ)) +
          (r_val ^ 2 - 2 * c₀ * r_val) := by
        rcases of_codeHasSinkOrWitness hk hk_bdd K' hsw with ⟨s, hs⟩ | ⟨hlt, hw⟩
        · exact css_ineq_of_universal_sink hn G₀ hG₀ hr_nn hreg_deg v_orig s (fun i hi => hs i hi)
        · exact css_ineq_of_commonOut_nonempty hn G₀ hG₀ hr_nn hreg_deg v_orig
            ⟨y ⟨k_orig, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hw i⟩⟩
      have hmul := mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg (rd : ℝ))) hcss
      have hident : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 *
          (((chiPairSet G₀ v_orig).card : ℝ) / ((n : ℝ) ^ 2) +
            2 * r_val * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ)) +
            (r_val ^ 2 - 2 * c₀ * r_val)) =
          1 * (rd : ℝ) ^ 2 * ((chiPairSet G₀ v_orig).card : ℝ) +
          2 * 1 * (rn : ℝ) * (rd : ℝ) * ((n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ)) +
          (n : ℝ) ^ 2 * (1 * (rn : ℝ) ^ 2 - c₀ * (2 * 1 * (rn : ℝ) * (rd : ℝ))) := by
        dsimp [r_val]
        have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
        have hrd0 : (rd : ℝ) ≠ 0 := hrd_pos.ne'
        have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hn0
        have hrd2 : (rd : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hrd0
        have h1 : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2) =
            (rd : ℝ) ^ 2 * ((chiPairSet G₀ v_orig).card : ℝ) := by
          have : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2) =
              (rd : ℝ) ^ 2 * ((chiPairSet G₀ v_orig).card : ℝ) * ((n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
          rw [this, div_self hn2]; ring
        have h2 : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ))) =
            2 * (rn : ℝ) * (rd : ℝ) * ((n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ)) := by
          have : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ))) =
              2 * (rn : ℝ) * (rd : ℝ) * (n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ) * ((rd : ℝ) / (rd : ℝ)) * ((n : ℝ) / (n : ℝ)) := by ring
          rw [this, div_self hrd0, div_self hn0]; ring
        have h3 : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (((rn : ℝ) / (rd : ℝ)) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))) =
            (n : ℝ) ^ 2 * ((rn : ℝ) ^ 2 - c₀ * (2 * (rn : ℝ) * (rd : ℝ))) := by
          rw [div_pow]
          have : (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * ((rn : ℝ) ^ 2 / (rd : ℝ) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))) =
              (n : ℝ) ^ 2 * ((rn : ℝ) ^ 2 * ((rd : ℝ) ^ 2 / (rd : ℝ) ^ 2) - 2 * c₀ * (rn : ℝ) * (rd : ℝ) * ((rd : ℝ) / (rd : ℝ))) := by ring
          rw [this, div_self hrd2, div_self hrd0]; ring
        calc (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 *
              (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2 +
                2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ)) +
                (((rn : ℝ) / (rd : ℝ)) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))))
            = (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2) +
              (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ))) +
              (n : ℝ) ^ 2 * (rd : ℝ) ^ 2 * (((rn : ℝ) / (rd : ℝ)) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))) := by ring
          _ = _ := by rw [h1, h2, h3]; ring
      dsimp [a_num, a_den]; linarith
    · -- Tier 2 (α = 5/6): a_num = 5, a_den = 6
      have hcss : 0 ≤ (5 / 6 : ℝ) * (((chiPairSet G₀ v_orig).card : ℝ) / ((n : ℝ) ^ 2)) +
          2 * r_val * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ)) +
          (r_val ^ 2 - 2 * c₀ * r_val) := by
        rcases of_codeHasSinkOrWitness hk hk_bdd K' hsw with ⟨s, hs⟩ | ⟨hlt, hw⟩
        · exact css56_ineq_of_universal_sink hn G₀ hG₀ hr_nn hreg_deg v_orig s (fun i hi => hs i hi)
        · exact css56_ineq_of_commonOut_nonempty hn G₀ hG₀ hr_nn hreg_deg v_orig
            ⟨y ⟨k_orig, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hw i⟩⟩
      have hmul := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
        (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg (rd : ℝ)))) hcss
      have hident : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) *
          ((5 / 6 : ℝ) * (((chiPairSet G₀ v_orig).card : ℝ) / ((n : ℝ) ^ 2)) +
            2 * r_val * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ)) +
            (r_val ^ 2 - 2 * c₀ * r_val)) =
          5 * (rd : ℝ) ^ 2 * ((chiPairSet G₀ v_orig).card : ℝ) +
          2 * 6 * (rn : ℝ) * (rd : ℝ) * ((n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ)) +
          (n : ℝ) ^ 2 * (6 * (rn : ℝ) ^ 2 - c₀ * (2 * 6 * (rn : ℝ) * (rd : ℝ))) := by
        dsimp [r_val]
        have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
        have hrd0 : (rd : ℝ) ≠ 0 := hrd_pos.ne'
        have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hn0
        have hrd2 : (rd : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hrd0
        have h1 : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * ((5 / 6 : ℝ) * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2)) =
            5 * (rd : ℝ) ^ 2 * ((chiPairSet G₀ v_orig).card : ℝ) := by
          have : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * ((5 / 6 : ℝ) * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2)) =
              5 * (rd : ℝ) ^ 2 * ((chiPairSet G₀ v_orig).card : ℝ) * ((n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
          rw [this, div_self hn2]; ring
        have h2 : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * (2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ))) =
            2 * 6 * (rn : ℝ) * (rd : ℝ) * ((n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ)) := by
          have : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * (2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ))) =
              12 * (rn : ℝ) * (rd : ℝ) * (n : ℝ) * ((srcStarSet G₀ v_orig).card : ℝ) * ((rd : ℝ) / (rd : ℝ)) * ((n : ℝ) / (n : ℝ)) := by ring
          rw [this, div_self hrd0, div_self hn0]; ring
        have h3 : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * (((rn : ℝ) / (rd : ℝ)) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))) =
            (n : ℝ) ^ 2 * (6 * (rn : ℝ) ^ 2 - c₀ * (2 * 6 * (rn : ℝ) * (rd : ℝ))) := by
          rw [div_pow]
          have : 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * ((rn : ℝ) ^ 2 / (rd : ℝ) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))) =
              (n : ℝ) ^ 2 * (6 * (rn : ℝ) ^ 2 * ((rd : ℝ) ^ 2 / (rd : ℝ) ^ 2) - 12 * c₀ * (rn : ℝ) * (rd : ℝ) * ((rd : ℝ) / (rd : ℝ))) := by ring
          rw [this, div_self hrd2, div_self hrd0]; ring
        calc 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) *
              ((5 / 6 : ℝ) * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2) +
                2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ)) +
                (((rn : ℝ) / (rd : ℝ)) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))))
            = 6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * ((5 / 6 : ℝ) * (((chiPairSet G₀ v_orig).card : ℝ) / (n : ℝ) ^ 2)) +
              6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * (2 * ((rn : ℝ) / (rd : ℝ)) * (((srcStarSet G₀ v_orig).card : ℝ) / (n : ℝ))) +
              6 * ((n : ℝ) ^ 2 * (rd : ℝ) ^ 2) * (((rn : ℝ) / (rd : ℝ)) ^ 2 - 2 * c₀ * ((rn : ℝ) / (rd : ℝ))) := by ring
          _ = _ := by rw [h1, h2, h3]
      dsimp [a_num, a_den]; linarith

end CaccettaHaggkvist
