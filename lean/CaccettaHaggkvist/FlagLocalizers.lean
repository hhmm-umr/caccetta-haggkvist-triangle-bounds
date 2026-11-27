module

public import CaccettaHaggkvist.ExpectationBridge
public import CaccettaHaggkvist.WeightedFlags

/-! # The local inequalities used by the six-vertex certificates

Conditioning on the roots leaves one free vertex in an induction term and two
in a CSS term. The root test includes both sink types and lifted witnesses.
-/

@[expose] public section

namespace CaccettaHaggkvist
namespace FlagLocalizer

noncomputable def indicator (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable P) 1 0

private theorem sum_indicator {T : Type*} [Fintype T] (s : Finset T) :
    ∑ x : T, indicator (x ∈ s) = (s.card : ℝ) := by
  classical
  have h (x : T) : indicator (x ∈ s) = (if x ∈ s then (1 : ℝ) else 0) := by
    by_cases hx : x ∈ s <;> simp [indicator, hx]
  simp_rw [h]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

noncomputable def inductionScore {k a : ℕ} (hk : a ≤ k) (c : ℝ)
    (K : OrientedGraph (Fin (k + 1))) : ℝ :=
  indicator (srcStarPred a hk K) + c * (indicator (allInPred a hk K) - 1)

noncomputable def cssScore {k a : ℕ} (hk : a ≤ k) (α r c : ℝ)
    (K : OrientedGraph (Fin (k + 2))) : ℝ :=
  α * indicator (chiPred2 a hk K) + 2*r * indicator (srcStarPred2 a hk K) +
    (r^2 - 2*r*c)

noncomputable def gated {k e : ℕ} (a : ℕ) (A : OrientedGraph (Fin (k + e)) → ℝ)
    (K : OrientedGraph (Fin (k + e))) : ℝ :=
  if codeHasSinkOrWitness a k (graphTritCode (K.pullback (Fin.castAdd e))) then A K else 0

theorem mean_gated {W : Type*} [Fintype W] {k e : ℕ} (a : ℕ) (w : W → ℝ)
    (G : OrientedGraph W) (A : OrientedGraph (Fin (k + e)) → ℝ) (x : Fin k → W) :
    WeightedFlag.mean w G (gated a A) x =
      if codeHasSinkOrWitness a k (graphTritCode (G.pullback x)) then
        WeightedFlag.mean w G A x else 0 := by
  have hp (z : Fin e → W) :
      (G.pullback (Fin.append x z)).pullback (Fin.castAdd e) = G.pullback x := by
    rw [OrientedGraph.pullback_comp]
    congr 1; funext j; simp
  unfold WeightedFlag.mean gated
  simp_rw [hp]
  split <;> simp_all

private theorem induction_mean {n k a : ℕ} (hn : 0 < n) (hk : a ≤ k) (G : OrientedGraph (Fin n))
    [DecidableRel G.adj] (c : ℝ) (x : Fin k → Fin n) :
    let v := x ∘ Fin.castLE hk
    WeightedFlag.mean (unifWeight (Fin n)) G (inductionScore hk c) x =
      ((srcStarSet G v).card : ℝ) / n + c * (((commonOutSet G v).card : ℝ) / n) - c := by
  let v := x ∘ Fin.castLE hk
  have sample (z : Fin 1 → Fin n) :
      inductionScore hk c (G.pullback (Fin.append x z)) =
        indicator (z 0 ∈ srcStarSet G v) + c * (indicator (z 0 ∈ commonOutSet G v) - 1) := by
    have hin (i : Fin a) :
        (G.pullback (Fin.append x z)).adj ⟨i.val, by omega⟩ (Fin.last k) ↔ G.adj (v i) (z 0) := by
      change G.adj (Fin.append x z (Fin.castAdd 1 (Fin.castLE hk i)))
        (Fin.append x z (Fin.natAdd k (0 : Fin 1))) ↔ _
      simp [v]
    have hout (i : Fin a) :
        (G.pullback (Fin.append x z)).adj (Fin.last k) ⟨i.val, by omega⟩ ↔ G.adj (z 0) (v i) := by
      change G.adj (Fin.append x z (Fin.natAdd k (0 : Fin 1)))
        (Fin.append x z (Fin.castAdd 1 (Fin.castLE hk i))) ↔ _
      simp [v]
    simp only [inductionScore, srcStarPred, allInPred, srcStarSet, commonOutSet,
      Finset.mem_filter, Finset.mem_univ, true_and, hin, hout]
  unfold WeightedFlag.mean
  rw [← Equiv.sum_comp (equivFin1 (Fin n))]
  simp_rw [sample, tupleWeight_unif_fin1]
  change (∑ z : Fin n, 1 / (n : ℝ) * (indicator (z ∈ srcStarSet G v) +
    c * (indicator (z ∈ commonOutSet G v) - 1))) = _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_indicator, sum_indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp
  ring

private theorem css_mean {n k a : ℕ} (hn : 0 < n) (hk : a ≤ k) (G : OrientedGraph (Fin n))
    [DecidableRel G.adj] (α r c : ℝ) (x : Fin k → Fin n) :
    let v := x ∘ Fin.castLE hk
    WeightedFlag.mean (unifWeight (Fin n)) G (cssScore hk α r c) x =
      α * (((chiPairSet G v).card : ℝ) / (n : ℝ)^2) +
      2*r * (((srcStarSet G v).card : ℝ) / n) + (r^2 - 2*c*r) := by
  let v := x ∘ Fin.castLE hk
  have sample (z : Fin 2 → Fin n) :
      cssScore hk α r c (G.pullback (Fin.append x z)) =
        α * indicator ((z 0,z 1) ∈ chiPairSet G v) +
        2*r * indicator (z 0 ∈ srcStarSet G v) + (r^2 - 2*r*c) := by
    have hp (i : Fin a) :
        Fin.append x z ⟨i.val, by omega⟩ = v i := Fin.append_left x z (Fin.castLE hk i)
    have h0 : Fin.append x z ⟨k, by omega⟩ = z 0 := Fin.append_right x z (0 : Fin 2)
    have h1 : Fin.append x z ⟨k+1, by omega⟩ = z 1 := Fin.append_right x z (1 : Fin 2)
    simp only [cssScore, chiPred2, srcStarPred2, chiPairSet, srcStarSet,
      Finset.mem_filter, Finset.mem_univ, true_and, OrientedGraph.pullback, hp, h0, h1]
  unfold WeightedFlag.mean
  rw [← Equiv.sum_comp (equivFin2 (Fin n))]
  simp_rw [sample, tupleWeight_unif_fin2]
  change (∑ p : Fin n × Fin n, 1 / (n : ℝ)^2 *
    (α * indicator (p ∈ chiPairSet G v) +
      2*r * indicator (p.1 ∈ srcStarSet G v) + (r^2 - 2*r*c))) = _
  have hs : (∑ p : Fin n × Fin n, indicator (p.1 ∈ srcStarSet G v)) =
      (n : ℝ) * ((srcStarSet G v).card : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_indicator]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_indicator, hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  push_cast
  field_simp
  ring

/-- This is the conditional hypothesis required by an induction-weighted SOS factor. -/
theorem induction_mean_ge {n k a : ℕ} (hn : 0 < n) (hk : a ≤ k) (hb : a ≤ 2^17)
    (G : OrientedGraph (Fin n)) [DecidableRel G.adj] (hG : G.TriangleFree)
    {c ε : ℝ} (hε : 0 ≤ ε) (hreg : ∀ w, (G.toDigraph.outDeg w : ℝ) = c * n)
    (hhered : ∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S,
      ((S ∩ G.toDigraph.outSet v).card : ℝ) ≤ (c + ε) * S.card) (x : Fin k → Fin n) :
    -ε ≤ WeightedFlag.mean (unifWeight (Fin n)) G (gated a (inductionScore hk c)) x := by
  rw [mean_gated]
  split
  next h =>
    rw [induction_mean hn]
    rcases of_codeHasSinkOrWitness hk hb (G.pullback x) h with ⟨s, hs⟩ | ⟨hax, hx⟩
    · exact ind_ineq_of_universal_sink hn G hG hε hreg hhered _ s hs
    · exact ind_ineq_of_commonOut_nonempty hn G hG hε hreg hhered _
        ⟨x ⟨a,hax⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  next => linarith

/-- The CSS-weighted factors have zero loss, including lifted nonsink types. -/
theorem css_mean_nonneg {n k a : ℕ} (hn : 0 < n) (hk : a ≤ k) (hb : a ≤ 2^17)
    (G : OrientedGraph (Fin n)) [DecidableRel G.adj] (hG : G.TriangleFree)
    {α c r : ℝ} (hα : (1037 / 1250 : ℝ) ≤ α) (hr : 0 ≤ r) (hreg : ∀ w, (G.toDigraph.outDeg w : ℝ) = c * n)
    (x : Fin k → Fin n) :
    0 ≤ WeightedFlag.mean (unifWeight (Fin n)) G (gated a (cssScore hk α r c)) x := by
  rw [mean_gated]
  split
  next h =>
    rw [css_mean hn]
    let v := x ∘ Fin.castLE hk
    have hχ := div_nonneg (Nat.cast_nonneg ((chiPairSet G v).card) : (0 : ℝ) ≤ _) (sq_nonneg (n : ℝ))
    have lift := mul_le_mul_of_nonneg_right hα hχ
    rcases of_codeHasSinkOrWitness hk hb (G.pullback x) h with ⟨s, hs⟩ | ⟨hax, hx⟩
    · have base := cssSharp_ineq_of_universal_sink hn G hG hr hreg v s hs
      linarith
    · have hU : (commonOutSet G v).Nonempty :=
        ⟨x ⟨a,hax⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
      have base := cssSharp_ineq_of_commonOut_nonempty hn G hG hr hreg v hU
      linarith
  next => exact le_rfl

end FlagLocalizer
end CaccettaHaggkvist
