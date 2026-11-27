module

public import CaccettaHaggkvist.FlagCert

/-! # Flag squares multiplied by a local graph inequality

The two copies of the flag and the local inequality share only their ordered
roots. Conditional on those roots, the three sets of free coordinates are
independent samples with replacement.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

namespace WeightedFlag

def roots (k d e : ℕ) (i : Fin k) : Fin (k + d + d + e) :=
  Fin.castAdd e (Fin.castAdd d (Fin.castAdd d i))

def left (k d e : ℕ) (i : Fin (k + d)) : Fin (k + d + d + e) :=
  Fin.castAdd e (Fin.castAdd d i)

def right (k d e : ℕ) : Fin (k + d) → Fin (k + d + d + e) :=
  Fin.append (roots k d e) (fun i => Fin.castAdd e (Fin.natAdd (k + d) i))

def localizer (k d e : ℕ) : Fin (k + e) → Fin (k + d + d + e) :=
  Fin.append (roots k d e) (Fin.natAdd (k + d + d))

/-- The ordered graph functional for one localized rank-one factor. -/
def term {k d e : ℕ} (A : OrientedGraph (Fin (k + e)) → ℝ)
    (F : OrientedGraph (Fin (k + d)) → ℝ) (H : OrientedGraph (Fin (k + d + d + e))) : ℝ :=
  A (H.pullback (localizer k d e)) * F (H.pullback (left k d e)) * F (H.pullback (right k d e))

/-- Average over the free vertices of a flag with root tuple fixed at `x`. -/
def mean {W : Type*} [Fintype W] {k a : ℕ} (w : W → ℝ) (G : OrientedGraph W)
    (F : OrientedGraph (Fin (k + a)) → ℝ) (x : Fin k → W) : ℝ :=
  ∑ y : Fin a → W, tupleWeight w y * F (G.pullback (Fin.append x y))

private theorem append_eq {W : Type*} {a b : ℕ} (x : Fin a → W) (y : Fin b → W) :
    appendTuple x y = Fin.append x y := by
  funext i
  cases i using Fin.addCases with
  | left j => simp [appendTuple, j.isLt]
  | right j =>
    have hn : ¬ a + j.val < a := by omega
    simp [appendTuple, hn]

private theorem split_sum {W : Type*} [Fintype W] {a b : ℕ}
    (f : (Fin (a + b) → W) → ℝ) :
    ∑ t, f t = ∑ x : Fin a → W, ∑ y : Fin b → W, f (Fin.append x y) := by
  obtain ⟨equiv, he⟩ := appendTuple_equiv (W := W) (a := a) (b := b)
  rw [← Equiv.sum_comp equiv, Fintype.sum_prod_type]
  simp_rw [he, append_eq]

private theorem weight_append {W : Type*} {a b : ℕ} (w : W → ℝ)
    (x : Fin a → W) (y : Fin b → W) :
    tupleWeight w (Fin.append x y) = tupleWeight w x * tupleWeight w y := by
  rw [← append_eq, tupleWeight_appendTuple]

/-- Each coefficient of a weighted SOS block contributes the conditional
localizer mean times a square. This also applies to tuples with repeated vertices. -/
theorem expectation_eq {W : Type*} [Fintype W] {k d e : ℕ}
    (w : W → ℝ) (G : OrientedGraph W) (A : OrientedGraph (Fin (k + e)) → ℝ)
    (F : OrientedGraph (Fin (k + d)) → ℝ) :
    ∑ t, tupleWeight w t * term A F (G.pullback t) =
      ∑ x : Fin k → W, tupleWeight w x * mean w G A x * (mean w G F x)^2 := by
  rw [split_sum (a := k + d + d) (b := e), split_sum (a := k + d) (b := d),
      split_sum (a := k) (b := d)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have factor (y z : Fin d → W) (v : Fin e → W) :
      let t := Fin.append (Fin.append (Fin.append x y) z) v
      tupleWeight w t * term A F (G.pullback t) =
        tupleWeight w x * (tupleWeight w y * F (G.pullback (Fin.append x y))) *
        (tupleWeight w z * F (G.pullback (Fin.append x z))) *
        (tupleWeight w v * A (G.pullback (Fin.append x v))) := by
    let t := Fin.append (Fin.append (Fin.append x y) z) v
    have hl : t ∘ left k d e = Fin.append x y := by
      funext i
      simp [Function.comp_apply, left, t]
    have hr : t ∘ right k d e = Fin.append x z := by
      funext i
      cases i using Fin.addCases <;> simp [Function.comp_apply, t, right, roots]
    have ha : t ∘ localizer k d e = Fin.append x v := by
      funext i
      cases i using Fin.addCases <;> simp [Function.comp_apply, t, localizer, roots]
    change tupleWeight w t * (A (G.pullback (t ∘ localizer k d e)) *
      F (G.pullback (t ∘ left k d e)) * F (G.pullback (t ∘ right k d e))) = _
    rw [ha, hl, hr]
    simp only [t, weight_append]
    ring
  dsimp only at factor
  let f (y : Fin d → W) := tupleWeight w y * F (G.pullback (Fin.append x y))
  let a (v : Fin e → W) := tupleWeight w v * A (G.pullback (Fin.append x v))
  have inner (y : Fin d → W) :
      (∑ z, ∑ v, tupleWeight w x * f y * f z * a v) =
        tupleWeight w x * f y * (∑ z, f z) * ∑ v, a v := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [factor]
  change (∑ y, ∑ z, ∑ v, tupleWeight w x * f y * f z * a v) =
    tupleWeight w x * (∑ v, a v) * (∑ y, f y)^2
  simp_rw [inner]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- A localizer with conditional mean at least `-ε` loses at most `B² ε` in
a weighted block with flag coefficients of absolute value at most `B`. A flag
with zero conditional mean at an ineligible root contributes zero. -/
theorem expectation_ge {W : Type*} [Fintype W] {k d e : ℕ}
    {w : W → ℝ} (hw : IsProbWeight w) (G : OrientedGraph W)
    (A : OrientedGraph (Fin (k + e)) → ℝ) (F : OrientedGraph (Fin (k + d)) → ℝ)
    {ε B : ℝ} (hε : 0 ≤ ε) (hF : ∀ K, |F K| ≤ B)
    (hA : ∀ x, mean w G F x = 0 ∨ -ε ≤ mean w G A x) :
    -(B^2) * ε ≤ ∑ t, tupleWeight w t * term A F (G.pullback t) := by
  rw [expectation_eq]
  have bounded (x : Fin k → W) : |mean w G F x| ≤ B := by
    calc
      |mean w G F x| ≤ ∑ y : Fin d → W, |tupleWeight w y * F (G.pullback (Fin.append x y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y : Fin d → W, tupleWeight w y * B := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (tupleWeight_nonneg hw y)]
        exact mul_le_mul_of_nonneg_left (hF _) (tupleWeight_nonneg hw y)
      _ = B := by rw [← Finset.sum_mul, sum_tupleWeight hw, one_mul]
  calc
    -(B^2) * ε = ∑ x : Fin k → W, tupleWeight w x * (-(B^2) * ε) := by
      rw [← Finset.sum_mul, sum_tupleWeight hw, one_mul]
    _ ≤ _ := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (tupleWeight_nonneg hw x)
      rcases hA x with hz | hl
      · rw [hz]
        nlinarith [mul_nonneg (sq_nonneg B) hε]
      · have hs : (mean w G F x)^2 ≤ B^2 := by
          simpa [← sq, sq_abs] using
            (mul_self_le_mul_self (abs_nonneg _) (bounded x))
        nlinarith [mul_nonneg (sub_nonneg.mpr hs) hε,
          mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (mean w G F x))]

end WeightedFlag

end CaccettaHaggkvist
