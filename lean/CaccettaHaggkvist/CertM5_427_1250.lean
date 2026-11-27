module

public import CaccettaHaggkvist.IntervalM5Bridge
public import CaccettaHaggkvist.CertM5_689_2000
public import CaccettaHaggkvist.CertM5_427_Data
public import CaccettaHaggkvist.CertM5_427_Tab
public import CaccettaHaggkvist.CertM5_427_M0
public import CaccettaHaggkvist.CertM5_427_M1
public import CaccettaHaggkvist.CertM5_427_M2
public import CaccettaHaggkvist.CertM5_427_M3

namespace CaccettaHaggkvist

private lemma check_models_427_1250 : cert_m5_427_1250.checkModelsSlice 0 317 = true := by
  refine cert_m5_427_1250.checkModelsSlice_of_forall fun gi hgi => ?_
  by_cases h0 : gi < 80
  · exact check_models_427_s0 (by omega) h0
  by_cases h1 : gi < 160
  · exact check_models_427_s1 (by omega) h1
  by_cases h2 : gi < 240
  · exact check_models_427_s2 (by omega) h2
  exact check_models_427_s3 (by omega) (by omega)

@[expose] public section

/-- **Unconditional Link-2 Two-Endpoint Interval Bound (`c = 427/1250 = 0.3416`)**:
Every finite nonempty simple digraph with minimum out-degree `≥ (427/1250) * |V|`
contains a directed cycle of length `≤ 3` (strictly beating HKN `0.3465` and Link-1 `0.3445`,
and anchoring the `m = 6` interval `[3383/10000, 427/1250]`). -/
theorem hasCycleLe3_of_minOutDeg_ge_427_1250
    {V : Type*} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj]
    (hdeg : ∀ u : V, ((427 : ℝ) / (1250 : ℝ)) * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) :
    G.HasCycleLe3 := by
  refine cert_m5_427_1250.hasCycleLe3 ?_ check_tables_427_1250 check_models_427_1250 G fun u => ?_
  · simpa [cert_m5_427_1250] using cStar_le_689_2000
  · simpa [cert_m5_427_1250] using hdeg u

/-- Global extremal bound `cStar ≤ 427 / 1250`, anchoring Stage-3 `m = 6` interval `[3383/10000, 427/1250]`! -/
theorem cStar_le_427_1250 : cStar ≤ (427 : ℝ) / (1250 : ℝ) :=
  cStar_le_of_hasCycleLe3 hasCycleLe3_of_minOutDeg_ge_427_1250

end

end CaccettaHaggkvist
