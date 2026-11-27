module

public import CaccettaHaggkvist.CanonCompleteness
public import CaccettaHaggkvist.CertM5_427_1250

/-! # Closing an affine interval on the six-vertex canonical models -/

@[expose] public section

namespace CaccettaHaggkvist

private def model6 (i : Fin 6583) := maskGraph 6 (models6Tree.get i.val)

/-- Lower bound for the expectation of an affine score on every extremal sample. -/
def SixVertexMeanBound (M : ℝ) (U V : OrientedGraph (Fin 6) → ℝ) : Prop :=
  ∀ {n : ℕ} (_ : 0 < n) {c ε : ℝ} (_ : 0 < ε)
      (G : OrientedGraph (Fin n)) (d : DecidableRel G.adj), G.TriangleFree →
      (∀ v, @Digraph.outWeight _ _ G.toDigraph d (unifWeight (Fin n)) v = c) →
      (∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S,
        ((S ∩ @Digraph.outSet _ _ G.toDigraph d v).card : ℝ) ≤ (c + ε) * S.card) →
      -M * ε ≤ ∑ x : Fin 6 → Fin n, tupleWeight (unifWeight (Fin n)) x *
        (U (G.pullback x) + c * V (G.pullback x))

/-- A strict check at both endpoints suffices. The finite model list supplies a uniform
positive margin and an absolute slope bound, including when the extremal ratio equals
the lower endpoint. The high endpoint can come from a preceding interval. -/
theorem hasCycleLe3_of_six_vertex_interval {lo hi M : ℝ}
    (hle : lo ≤ hi) (hupper : cStar ≤ hi) (hM : 0 ≤ M)
    (U V : OrientedGraph (Fin 6) → ℝ)
    (hmean : SixVertexMeanBound M U V)
    (hends : ∀ i : Fin 6583,
      symPerm (fun K => U K + lo * V K) (maskGraph 6 (models6Tree.get i.val)) < 0 ∧
      symPerm (fun K => U K + hi * V K) (maskGraph 6 (models6Tree.get i.val)) < 0)
    {W : Type*} [Fintype W] [Nonempty W] (G : Digraph W) [DecidableRel G.adj]
    (hdeg : ∀ v, lo * Fintype.card W ≤ (G.outDeg v : ℝ)) : G.HasCycleLe3 := by
  let score (c : ℝ) (i : Fin 6583) := symPerm (fun K => U K + c * V K) (model6 i)
  let margin (i : Fin 6583) := min (-score lo i) (-score hi i)
  let slope (i : Fin 6583) := |symPerm V (model6 i)|
  let δ := Finset.univ.inf' Finset.univ_nonempty margin
  let L := Finset.univ.sup' Finset.univ_nonempty slope
  have hδ : 0 < δ := by
    change 0 < Finset.univ.inf' Finset.univ_nonempty margin
    rw [Finset.lt_inf'_iff]
    intro i _
    exact lt_min (neg_pos.mpr (hends i).1) (neg_pos.mpr (hends i).2)
  have hmargin (i : Fin 6583) : δ ≤ margin i := Finset.inf'_le _ (Finset.mem_univ i)
  have hslope (i : Fin 6583) : slope i ≤ L := Finset.le_sup' _ (Finset.mem_univ i)
  have hbounds (H : OrientedGraph (Fin 6)) (hH : H.TriangleFree) :
      symPerm (fun K => U K + lo * V K) H ≤ -δ ∧
      symPerm (fun K => U K + hi * V K) H ≤ -δ ∧ |symPerm V H| ≤ L := by
    obtain ⟨i, hidx, π, hπ⟩ := canon_completeness_6 H hH
    let j : Fin 6583 := ⟨i, hidx⟩
    have transfer (F : OrientedGraph (Fin 6) → ℝ) : symPerm F H = symPerm F (model6 j) := by
      rw [← symPerm_relabel F H π, hπ]
      rfl
    rw [transfer (fun K => U K + lo * V K), transfer (fun K => U K + hi * V K),
      transfer V]
    have hlo := (hmargin j).trans (min_le_left _ _)
    have hhi := (hmargin j).trans (min_le_right _ _)
    change δ ≤ -symPerm (fun K => U K + lo * V K) (model6 j) at hlo
    change δ ≤ -symPerm (fun K => U K + hi * V K) (model6 j) at hhi
    exact ⟨by linarith, by linarith, hslope j⟩
  exact hasCycleLe3_of_interval_certificate hle hupper hM U V hmean hδ
    ((abs_nonneg _).trans (hslope 0)) (fun H hH => (hbounds H hH).1)
    (fun H hH => (hbounds H hH).2.1) (fun H hH => (hbounds H hH).2.2) G hdeg

/-- Specialization at the exact five-vertex upper endpoint. -/
theorem hasCycleLe3_of_six_vertex_certificate {lo M : ℝ}
    (hle : lo ≤ 427 / 1250) (hM : 0 ≤ M)
    (U V : OrientedGraph (Fin 6) → ℝ)
    (hmean : SixVertexMeanBound M U V)
    (hends : ∀ i : Fin 6583,
      symPerm (fun K => U K + lo * V K) (maskGraph 6 (models6Tree.get i.val)) < 0 ∧
      symPerm (fun K => U K + (427 / 1250 : ℝ) * V K) (maskGraph 6 (models6Tree.get i.val)) < 0)
    {W : Type*} [Fintype W] [Nonempty W] (G : Digraph W) [DecidableRel G.adj]
    (hdeg : ∀ v, lo * Fintype.card W ≤ (G.outDeg v : ℝ)) : G.HasCycleLe3 :=
  hasCycleLe3_of_six_vertex_interval hle cStar_le_427_1250 hM U V hmean hends G hdeg

/-- A zero slack at the lower endpoint is sufficient for a bound on the
supremum. At every strictly interior point the affine scores are strictly negative. -/
theorem cStar_le_of_six_vertex_interval {lo hi M : ℝ}
    (hupper : cStar ≤ hi) (hM : 0 ≤ M) (U V : OrientedGraph (Fin 6) → ℝ)
    (hmean : SixVertexMeanBound M U V)
    (hends : ∀ i : Fin 6583,
      symPerm (fun K => U K + lo * V K) (maskGraph 6 (models6Tree.get i.val)) ≤ 0 ∧
      symPerm (fun K => U K + hi * V K) (maskGraph 6 (models6Tree.get i.val)) < 0) :
    cStar ≤ lo := by
  by_contra! hlt
  let mid := (lo + cStar) / 2
  have hmlo : lo < mid := by dsimp [mid]; linarith
  have hms : mid < cStar := by dsimp [mid]; linarith
  have hmhi := hms.le.trans hupper
  have hmid : cStar ≤ mid := by
    apply cStar_le_of_hasCycleLe3
    apply hasCycleLe3_of_six_vertex_interval hmhi hupper hM U V hmean
    intro i
    refine ⟨?_, (hends i).2⟩
    let H := maskGraph 6 (models6Tree.get i.val)
    have lin (c : ℝ) : symPerm (fun K => U K + c * V K) H =
        symPerm U H + c * symPerm V H := by
      unfold symPerm
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    obtain ⟨hlo, hhi⟩ := hends i
    change symPerm (fun K => U K + lo * V K) H ≤ 0 at hlo
    change symPerm (fun K => U K + hi * V K) H < 0 at hhi
    change symPerm (fun K => U K + mid * V K) H < 0
    rw [lin] at hlo hhi ⊢
    by_cases hs : 0 ≤ symPerm V H
    · linarith [mul_le_mul_of_nonneg_right hmhi hs]
    · linarith [mul_lt_mul_of_neg_right hmlo (lt_of_not_ge hs)]
  exact (not_le_of_gt hms) hmid

end CaccettaHaggkvist
