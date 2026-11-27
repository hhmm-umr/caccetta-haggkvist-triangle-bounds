import CaccettaHaggkvist
import Lean.Util.CollectAxioms

open Lean CaccettaHaggkvist

run_cmd
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let results := #[
    ``hasCycleLe3_of_minOutDeg_ge_689_2000, ``hasCycleLe3_of_minOutDeg_ge_427_1250,
    ``cStar_le_427_1250, ``OrientedGraph.exists_outDeg_lt_427_1250,
    ``canon_completeness_6, ``hasCycleLe3_of_six_vertex_certificate,
    ``WeightedFlag.expectation_eq, ``WeightedFlag.expectation_ge,
    ``OrientedGraph.exists_feedback_200_card_le_83_ordNonEdges,
    ``OrientedGraph.hundred_outDeg_sq_le_83_ordNonEdges,
    ``Digraph.exists_feedback_200_card_le_83_ordNonEdges,
    ``OrientedGraph.exists_outDeg_le_third_of_forb_TC_OP_F5,
    ``OrientedGraph.exists_outDeg_le_third_of_forb_4patterns,
    ``Digraph.exists_outDeg_le_third_of_forb_4patterns,
    ``SharpObstructions.obstructionP1_sharp, ``SharpObstructions.obstructionP2_sharp,
    ``SharpObstructions.obstructionP3_sharp, ``SharpObstructions.obstructionP4_sharp,
    ``rainbow_triangle_of_ch_bound, ``rainbow_triangle_12457_31250,
    ``rainbow_triangle_797_2000, ``rainbow_triangle_39849_100000,
    ``rainbow_triangle_79697_200000]
  for name in results do
    let deps ← collectAxioms name
    let extra := deps.filter fun ax => !allowed.contains ax
    unless extra.isEmpty do
      throwError "{name} uses additional axioms {extra}"
  logInfo m!"Checked {results.size} public declarations for nonstandard axioms."
