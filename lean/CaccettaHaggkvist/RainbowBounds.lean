module

public import CaccettaHaggkvist.CertM5_427_1250
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

end CaccettaHaggkvist
