module

public import CaccettaHaggkvist.CertM5Refined
public import CaccettaHaggkvist.Lexicographic
public import CaccettaHaggkvist.RainbowTriangle

/-! # Rainbow triangles from the five-vertex interval certificate -/

@[expose] public section

namespace CaccettaHaggkvist

universe u v

/-- Strict out-degree form of the unconditional five-vertex certificate. -/
theorem OrientedGraph.exists_outDeg_lt_427_1250
    {W : Type u} [Fintype W] [Nonempty W]
    (H : OrientedGraph W) [DecidableRel H.adj] (hH : H.TriangleFree) :
    ∃ w : W, (H.toDigraph.outDeg w : ℝ) < (427 / 1250 : ℝ) * Fintype.card W := by
  by_contra! hall
  exact hH (H.hasCycleLe3_iff_hasDirTriangle.mp
    (hasCycleLe3_of_minOutDeg_ge_427_1250 H.toDigraph hall))

/-- At least `n` colors, each with at least `0.398624 n` edges, force a rainbow triangle. -/
theorem rainbow_triangle_12457_31250
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C) (hC : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, (12457 / 31250 : ℝ) * Fintype.card V ≤ (G.colorEdges c).card) :
    G.HasRainbowTriangle :=
  rainbow_triangle_of_ch_bound (c_CH := 427 / 1250) (t := 12457 / 31250) (δ := 2181 / 50000)
    (fun H _ hH => H.exists_outDeg_lt_427_1250 hH)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) G hC hsize

/-- The refined five-vertex interval implies the unconditional rainbow threshold 0.398622. -/
theorem rainbow_triangle_199311_500000
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C) (hC : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, (199311 / 500000 : ℝ) * Fintype.card V ≤ (G.colorEdges c).card) :
    G.HasRainbowTriangle := by
  apply rainbow_triangle_of_ch_bound (c_CH := 3415403 / 10000000) (δ := 437 / 10000)
    _ _ _ _ _ _ _ _ G hC hsize
  · intro W _ _ _ H _ hH
    obtain ⟨v,h⟩ := H.exists_outDeg_le_pred_of_cStar_le hH cStar_le_3415403_10000000
    exact ⟨v,by linarith⟩
  all_goals norm_num

/-- Specialization of the reduction at the split six-vertex interval. -/
theorem rainbow_triangle_4981_12500
    (h_CH : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ v, (H.toDigraph.outDeg v : ℝ) < (33823/100000 : ℝ) * Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C) (hC : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, (4981 / 12500 : ℝ) * Fintype.card V ≤ (G.colorEdges c).card) :
    G.HasRainbowTriangle :=
  rainbow_triangle_of_ch_bound (c_CH := 33823 / 100000) (t := 4981 / 12500) (δ := 241 / 5000)
    h_CH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) G hC hsize

end CaccettaHaggkvist
