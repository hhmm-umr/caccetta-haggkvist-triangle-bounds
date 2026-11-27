import CaccettaHaggkvist
import Lean.Util.CollectAxioms

open Lean CaccettaHaggkvist

run_cmd
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let results := #[
    ``hasCycleLe3_of_minOutDeg_ge_689_2000, ``hasCycleLe3_of_minOutDeg_ge_427_1250,
    ``cStar_le_427_1250, ``OrientedGraph.exists_outDeg_lt_427_1250,
    ``hasCycleLe3_of_minOutDeg_ge_3415403_10000000, ``cStar_le_3415403_10000000,
    ``OrientedGraph.minOutDeg_le_cStar_card_sub_one, ``hasCycleLe3_of_cStar_le,
    ``hasCycleLe3_of_third_of_order_rounding, ``hasCycleLe3_of_third_of_five_vertex_order,
    ``hasCycleLe3_of_third_of_six_vertex_order,
    ``cStar_le_of_six_vertex_interval, ``CertificateGram.Packing.sound,
    ``SixVertex.Program.expectation_ge, ``SixVertex.cStar_le_of_program,
    ``SixVertex.fastModelRow_eq, ``SixVertex.permutationTable_checked,
    ``SixVertex.groupedRow_eq, ``SixVertex.Geometry.packedRow_eq,
    ``FlagLocalizer.induction_mean_ge, ``FlagLocalizer.css_mean_nonneg,
    ``OrientedGraph.exists_feedback_2500_card_le_1037_ordNonEdges,
    ``Digraph.exists_feedback_2500_card_le_1037_ordNonEdges, ``OrientedGraph.outDeg_sq_le_1037_ordNonEdges,
    ``OrientedGraph.degree_excess_le_twice_deleted, ``OrientedGraph.exists_disjoint_critical_patterns,
    ``rainbow_triangle_199311_500000, ``rainbow_triangle_4981_12500,
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
