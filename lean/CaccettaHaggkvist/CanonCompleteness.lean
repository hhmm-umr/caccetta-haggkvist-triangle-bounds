module

public import CaccettaHaggkvist.KernelCore
public import CaccettaHaggkvist.CanonModels
public import CaccettaHaggkvist.CanonStep2to5
public import CaccettaHaggkvist.CanonStep6_0
public import CaccettaHaggkvist.CanonStep6_1
public import CaccettaHaggkvist.CanonStep6_2
public import CaccettaHaggkvist.CanonStep6_3
public import CaccettaHaggkvist.CanonStep6_4
public import CaccettaHaggkvist.CanonStep6_5
public import CaccettaHaggkvist.CanonStep6_6
public import CaccettaHaggkvist.CanonStep6_7
public import CaccettaHaggkvist.CanonStep6_8
public import CaccettaHaggkvist.CanonStep6_9
public import CaccettaHaggkvist.CanonStep6_10
public import CaccettaHaggkvist.CanonStep6_11
public import CaccettaHaggkvist.CanonStep6_12
public import CaccettaHaggkvist.CanonStep6_13
public import CaccettaHaggkvist.CanonStep6_14
public import CaccettaHaggkvist.CanonStep6_15

@[expose] public section

namespace CaccettaHaggkvist

theorem witness_step6_all (idx : ℕ) (hlt : idx < 317 * 3 ^ 5) :
    ∃ w : ℕ, checkWitnessVal 5 6583 models5Tree models6Tree idx w = true := by
  by_cases h0 : idx < 4815
  · exact witness_step6_shard0 (by omega) h0
  by_cases h1 : idx < 9630
  · exact witness_step6_shard1 (by omega) h1
  by_cases h2 : idx < 14445
  · exact witness_step6_shard2 (by omega) h2
  by_cases h3 : idx < 19260
  · exact witness_step6_shard3 (by omega) h3
  by_cases h4 : idx < 24075
  · exact witness_step6_shard4 (by omega) h4
  by_cases h5 : idx < 28890
  · exact witness_step6_shard5 (by omega) h5
  by_cases h6 : idx < 33705
  · exact witness_step6_shard6 (by omega) h6
  by_cases h7 : idx < 38520
  · exact witness_step6_shard7 (by omega) h7
  by_cases h8 : idx < 43335
  · exact witness_step6_shard8 (by omega) h8
  by_cases h9 : idx < 48150
  · exact witness_step6_shard9 (by omega) h9
  by_cases h10 : idx < 52965
  · exact witness_step6_shard10 (by omega) h10
  by_cases h11 : idx < 57780
  · exact witness_step6_shard11 (by omega) h11
  by_cases h12 : idx < 62595
  · exact witness_step6_shard12 (by omega) h12
  by_cases h13 : idx < 67410
  · exact witness_step6_shard13 (by omega) h13
  by_cases h14 : idx < 72225
  · exact witness_step6_shard14 (by omega) h14
  exact witness_step6_shard15 (by omega) (by omega)

/-- **Complete Canonical Classification at `m = 6`**:
Every `C₃`-free `OrientedGraph (Fin 6)` is isomorphic (`relabel`) to one of the 6,583
canonical models in `models6Tree`! -/
theorem canon_completeness_6 (H : OrientedGraph (Fin 6)) (hH : H.TriangleFree) :
    ∃ gi, gi < 6583 ∧ ∃ π : Equiv.Perm (Fin 6), H.relabel π = maskGraph 6 (models6Tree.get gi) :=
  canon_completeness_step canon_completeness_5 witness_step6_all H hH

end CaccettaHaggkvist
