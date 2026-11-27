module

public import CaccettaHaggkvist.CertificateGram
public import CaccettaHaggkvist.FlagLocalizers

/-! # Integer programs for affine six-vertex certificates

An instruction supplies either an out-regularity multiplier, a nonnegative
root weight times a localizer, or a checked Gram block times a localizer.
The interpretation at parameter `c` is the intercept plus `c` times the slope.
-/

@[expose] public section

namespace CaccettaHaggkvist.SixVertex

def tritCode : (n : ℕ) → (K : OrientedGraph (Fin n)) → [DecidableRel K.adj] → ℕ
  | 0, _, _ => 0
  | n+1, K, _ =>
    packTrits (fun i => if K.adj i.castSucc (Fin.last n) then 1
      else if K.adj (Fin.last n) i.castSucc then 2 else 0) +
      3^n * tritCode n (K.pullback Fin.castSucc)

theorem tritCode_eq {n : ℕ} (K : OrientedGraph (Fin n)) [DecidableRel K.adj] :
    tritCode n K = graphTritCode K := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tritCode, graphTritCode, ih]
    congr 2
    funext i
    by_cases e : K.adj i.castSucc (Fin.last n)
    · simp [edgeTritG, e]
    · by_cases f : K.adj (Fin.last n) i.castSucc <;> simp [edgeTritG, e, f]

def bit (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

private theorem bit_real (P : Prop) [Decidable P] : ((bit P : ℤ) : ℝ) = FlagLocalizer.indicator P := by
  by_cases h : P <;> simp [bit, FlagLocalizer.indicator, h]

instance {k a : ℕ} (hk : a ≤ k) (K : OrientedGraph (Fin (k+1))) [DecidableRel K.adj] :
    Decidable (allInPred a hk K) := by unfold allInPred; infer_instance
instance {k a : ℕ} (hk : a ≤ k) (K : OrientedGraph (Fin (k+1))) [DecidableRel K.adj] :
    Decidable (srcStarPred a hk K) := by unfold srcStarPred; infer_instance
instance {k a : ℕ} (hk : a ≤ k) (K : OrientedGraph (Fin (k+2))) [DecidableRel K.adj] :
    Decidable (chiPred2 a hk K) := by unfold chiPred2; dsimp only; infer_instance
instance {k a : ℕ} (hk : a ≤ k) (K : OrientedGraph (Fin (k+2))) [DecidableRel K.adj] :
    Decidable (srcStarPred2 a hk K) := by unfold srcStarPred2; dsimp only; infer_instance

def atRatio (z : ℤ × ℤ) (c : ℝ) : ℝ := (z.1 : ℝ) + c * (z.2 : ℝ)

inductive Local (k : ℕ) : ℕ → Type
  | one : Local k 0
  | inductionTerm (a : Fin 7) (hk : a.val ≤ k) : Local k 1
  | css (a : Fin 7) (hk : a.val ≤ k) (p q rn rd : ℕ)
      (hq : 0 < q) (hrd : 0 < rd) (hα : 1037*q ≤ 1250*p) : Local k 2

def Local.error {k e : ℕ} : Local k e → ℕ
  | .inductionTerm .. => 1
  | _ => 0

def Local.eval {k : ℕ} : {e : ℕ} → Local k e → (K : OrientedGraph (Fin (k+e))) →
    [DecidableRel K.adj] → ℤ × ℤ
  | _, .one, _, _ => (1,0)
  | _, .inductionTerm a hk, K, _ =>
    if codeHasSinkOrWitness a k (tritCode k (K.pullback (Fin.castAdd 1))) then
      (bit (srcStarPred a hk K), bit (allInPred a hk K) - 1)
    else (0,0)
  | _, .css a hk p q rn rd _ _ _, K, _ =>
    if codeHasSinkOrWitness a k (tritCode k (K.pullback (Fin.castAdd 2))) then
      let slope : ℤ := 2 * q * rn * rd
      (p * (rd : ℤ)^2 * bit (chiPred2 a hk K) + slope * bit (srcStarPred2 a hk K) + q * (rn : ℤ)^2,
        -slope)
    else (0,0)

noncomputable def Local.real {k e : ℕ} (L : Local k e) (c : ℝ)
    (K : OrientedGraph (Fin (k+e))) : ℝ :=
  atRatio (@Local.eval k e L K (fun _ _ => Classical.propDecidable _)) c

theorem Local.at_eval {k e : ℕ} (L : Local k e) (c : ℝ) (K : OrientedGraph (Fin (k+e)))
    [d : DecidableRel K.adj] : atRatio (L.eval K) c = L.real c K := by
  unfold real
  rw [Subsingleton.elim d (fun _ _ => Classical.propDecidable _)]

theorem Local.mean_ge {n k e : ℕ} (hn : 0 < n) (L : Local k e)
    (G : OrientedGraph (Fin n)) [DecidableRel G.adj] (hG : G.TriangleFree)
    {c ε : ℝ} (hε : 0 ≤ ε) (hreg : ∀ w, (G.toDigraph.outDeg w : ℝ) = c*n)
    (hhered : ∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S,
      ((S ∩ G.toDigraph.outSet v).card : ℝ) ≤ (c+ε)*S.card) (x : Fin k → Fin n) :
    -(L.error : ℝ) * ε ≤ WeightedFlag.mean (unifWeight (Fin n)) G (L.real c) x := by
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  cases L with
  | one =>
    simp [WeightedFlag.mean, Local.real, Local.eval, Local.error, atRatio, tupleWeight]
  | inductionTerm a hk =>
    have eqn : (Local.inductionTerm a hk).real c =
        FlagLocalizer.gated a (FlagLocalizer.inductionScore hk c) := by
      funext K
      simp only [Local.real, Local.eval, tritCode_eq, FlagLocalizer.gated]
      split <;> simp [atRatio, FlagLocalizer.inductionScore, bit_real]
    rw [eqn]
    simpa [Local.error] using
      FlagLocalizer.induction_mean_ge hn hk (by omega) G hG hε hreg hhered x
  | css a hk p q rn rd hq hrd ha =>
    have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hr' : (0 : ℝ) < rd := Nat.cast_pos.mpr hrd
    have hα : (1037 / 1250 : ℝ) ≤ p / q := by
      rw [div_le_div_iff₀ (by norm_num) hq']
      exact_mod_cast (by simpa [Nat.mul_comm p 1250] using ha : 1037*q ≤ p*1250)
    have eqn : (Local.css a hk p q rn rd hq hrd ha).real c = fun K =>
        ((q : ℝ) * rd^2) * FlagLocalizer.gated a
          (FlagLocalizer.cssScore hk (p / q) (rn / rd) c) K := by
      funext K
      simp only [Local.real, Local.eval, tritCode_eq, FlagLocalizer.gated]
      split
      · simp only [atRatio, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          Int.cast_neg, Int.cast_ofNat, bit_real, FlagLocalizer.cssScore]
        field_simp
        ring
      · simp [atRatio]
    rw [eqn]
    have h := FlagLocalizer.css_mean_nonneg hn hk (by omega) G hG hα
      (div_nonneg (Nat.cast_nonneg rn) hr'.le) hreg x
    have pull (f : OrientedGraph (Fin (k+2)) → ℝ) (a : ℝ) :
        WeightedFlag.mean (unifWeight (Fin n)) G (fun K => a * f K) x =
          a * WeightedFlag.mean (unifWeight (Fin n)) G f x := by
      unfold WeightedFlag.mean
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [pull]
    simpa [Local.error] using mul_nonneg (mul_nonneg hq'.le (sq_nonneg (rd : ℝ))) h

structure RootWeight where
  cap : ℕ
  table : ℕ → ℕ

def RootWeight.read (w : RootWeight) (word : ℕ) := min w.cap (w.table word)

inductive Term : ℕ → Type
  | degree (r : ℕ) (f : ℕ → ℤ) : Term (r+2)
  | linear {k e : ℕ} (L : Local k e) (w : RootWeight) : Term (k+e)
  | gram (k d e : ℕ) (L : Local k e) (B : CertificateGram) : Term (k+d+d+e)

def Term.check {m : ℕ} : Term m → Bool
  | .gram _ _ _ _ B => B.check
  | _ => true

noncomputable def Term.loss {m : ℕ} : Term m → ℝ
  | .degree .. => 0
  | .linear L w => w.cap * (L.error : ℝ)
  | .gram _ _ _ L B => B.loss * (L.error : ℝ)

def scale (w : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (w*z.1,w*z.2)

def Term.eval : {m : ℕ} → Term m → (H : OrientedGraph (Fin m)) →
    [DecidableRel H.adj] → ℤ × ℤ
  | _, .degree r f, H, _ =>
    let a := f (tritCode (r+1) (H.pullback embSkipOne))
    (a * bit (H.adj 0 1), -a)
  | _, .linear L w, H, _ =>
    scale (w.read (tritCode _ (H.pullback (Fin.castAdd _)))) (L.eval H)
  | _, .gram k d e L B, H, _ =>
    scale (B.value (tritCode _ (H.pullback (WeightedFlag.left k d e)))
        (tritCode _ (H.pullback (WeightedFlag.right k d e))))
      (L.eval (H.pullback (WeightedFlag.localizer k d e)))

noncomputable def Term.real {m : ℕ} (t : Term m) (c : ℝ) (K : OrientedGraph (Fin m)) : ℝ :=
  atRatio (@Term.eval m t K (fun _ _ => Classical.propDecidable _)) c

theorem Term.loss_nonneg {m : ℕ} (t : Term m) : 0 ≤ t.loss := by
  cases t with
  | degree => exact le_rfl
  | linear => exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  | gram _ _ _ _ B => exact mul_nonneg B.loss_nonneg (Nat.cast_nonneg _)

private theorem scale_real (w : ℤ) (z : ℤ × ℤ) (c : ℝ) :
    atRatio (scale w z) c = (w : ℝ) * atRatio z c := by
  simp only [scale, atRatio, Int.cast_mul]; ring

theorem Term.expectation_ge {m n : ℕ} (t : Term m) (ht : t.check = true) (hn : 0 < n)
    (G : OrientedGraph (Fin n)) [DecidableRel G.adj] (hG : G.TriangleFree)
    {c ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ v, G.toDigraph.outWeight (unifWeight (Fin n)) v = c)
    (hhered : ∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S,
      ((S ∩ G.toDigraph.outSet v).card : ℝ) ≤ (c+ε)*S.card) :
    -t.loss * ε ≤ ∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x * t.real c (G.pullback x) := by
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hw : IsProbWeight (unifWeight (Fin n)) := isProbWeight_unifWeight
  have deg (v : Fin n) : (G.toDigraph.outDeg v : ℝ) = c*n := by
    have h := hreg v
    rwa [Digraph.outWeight_unifWeight, Fintype.card_fin, div_eq_iff (by positivity : (n:ℝ) ≠ 0)] at h
  cases t with
  | degree r f =>
    let g := fun K : OrientedGraph (Fin (r+1)) => (f (graphTritCode K) : ℝ)
    have eqn : (Term.degree r f).real c = fun K => degAffineU g K + c * degAffineV g K := by
      funext K
      simp only [Term.real, Term.eval, atRatio, Int.cast_mul, Int.cast_neg, bit_real, tritCode_eq]
      rfl
    rw [eqn, expect_degAffine_eq_zero G hw hreg]
    simp [Term.loss]
  | @linear k e L w =>
    let g := fun K : OrientedGraph (Fin k) => (w.read (graphTritCode K) : ℝ)
    have eqn : (Term.linear L w).real c = fun K => g (K.pullback (Fin.castAdd e)) * L.real c K := by
      funext K
      simp only [Term.real, Term.eval, scale_real, tritCode_eq, Int.cast_natCast, Local.at_eval, g]
    rw [eqn, WeightedFlag.sum_eq_mean (k := k) (e := e) (unifWeight (Fin n)) G
      (fun K => g (K.pullback (Fin.castAdd e)) * L.real c K)]
    simp_rw [WeightedFlag.mean_mul_root]
    calc
      -(Term.linear L w).loss * ε = ∑ x : Fin k → Fin n, tupleWeight (unifWeight _) x *
          (-(w.cap : ℝ) * ((L.error : ℝ)*ε)) := by
            rw [← Finset.sum_mul, sum_tupleWeight hw, one_mul]; unfold Term.loss; ring
      _ ≤ _ := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (tupleWeight_nonneg hw x)
        have h := L.mean_ge hn G hG hε deg hhered x
        have hle : g (G.pullback x) ≤ w.cap := Nat.cast_le.mpr (min_le_left _ _)
        have hnn : 0 ≤ g (G.pullback x) := Nat.cast_nonneg _
        nlinarith [mul_nonneg hnn (sub_nonneg.mpr h),
          mul_nonneg (sub_nonneg.mpr hle) (mul_nonneg (Nat.cast_nonneg L.error) hε)]
  | gram k d e L B =>
    have eqn : (Term.gram k d e L B).real c = B.term (L.real c) := by
      funext K
      simp only [Term.real, Term.eval, scale_real, tritCode_eq, CertificateGram.term, Local.at_eval]
      ring
    rw [eqn]
    have h := B.expectation_ge (d := d) ht hw G (L.real c)
      (mul_nonneg (Nat.cast_nonneg L.error) hε) (fun x => by
        simpa only [neg_mul] using L.mean_ge hn G hG hε deg hhered x)
    calc -(Term.gram k d e L B).loss * ε = -B.loss * ((L.error : ℝ)*ε) := by unfold Term.loss; ring
         _ ≤ _ := h

abbrev Program := List (Term 6)

def Program.eval (P : Program) (H : OrientedGraph (Fin 6)) [DecidableRel H.adj] : ℤ × ℤ :=
  P.foldr (fun t tail =>
    let z := t.eval H
    (z.1 + tail.1, z.2 + tail.2)) (0,0)

def Program.check (P : Program) : Bool := P.all Term.check

noncomputable def Program.loss (P : Program) : ℝ := (P.map Term.loss).sum

theorem Program.loss_nonneg (P : Program) : 0 ≤ P.loss := by
  induction P with
  | nil => exact le_rfl
  | cons t ts ih => exact add_nonneg t.loss_nonneg ih

noncomputable def Program.score (P : Program) (H : OrientedGraph (Fin 6)) : ℤ × ℤ :=
  @Program.eval P H (fun _ _ => Classical.propDecidable _)

/-- Assembly discharges the extremal expectation obligation for every program
whose finite Gram checks pass. The same integer scores enter endpoint reflection. -/
theorem Program.expectation_ge {n : ℕ} (P : Program) (hp : P.check = true) (hn : 0 < n)
    (G : OrientedGraph (Fin n)) [DecidableRel G.adj] (hG : G.TriangleFree)
    {c ε : ℝ} (hε : 0 ≤ ε) (hreg : ∀ v, G.toDigraph.outWeight (unifWeight (Fin n)) v = c)
    (hhered : ∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S,
      ((S ∩ G.toDigraph.outSet v).card : ℝ) ≤ (c+ε)*S.card) :
    -P.loss*ε ≤ ∑ x : Fin 6 → Fin n, tupleWeight (unifWeight (Fin n)) x *
      atRatio (P.score (G.pullback x)) c := by
  induction P with
  | nil => simp [loss, score, eval, atRatio]
  | cons t ts ih =>
    have both : t.check = true ∧ Program.check ts = true := by
      simpa only [Program.check, List.all_cons, Bool.and_eq_true] using hp
    have split (x : Fin 6 → Fin n) :
        tupleWeight (unifWeight (Fin n)) x * atRatio (Program.score (t :: ts) (G.pullback x)) c =
        tupleWeight (unifWeight (Fin n)) x * t.real c (G.pullback x) +
        tupleWeight (unifWeight (Fin n)) x * atRatio (Program.score ts (G.pullback x)) c := by
      simp only [score, eval, List.foldr_cons, atRatio, Term.real, Int.cast_add]
      ring
    simp_rw [split]
    rw [Finset.sum_add_distrib]
    have h := t.expectation_ge both.1 hn G hG hε hreg hhered
    have hrest := ih both.2
    change -(t.loss + Program.loss ts)*ε ≤ _
    linarith

end CaccettaHaggkvist.SixVertex
