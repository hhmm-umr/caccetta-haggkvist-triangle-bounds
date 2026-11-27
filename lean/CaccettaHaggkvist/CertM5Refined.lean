module

public import CaccettaHaggkvist.CertM5_427_1250

/-! # Retargeting the five-vertex interval with the original SOS factors -/

namespace CaccettaHaggkvist

private def refined : IntervalM5Cert :=
  {cert_m5_427_1250 with cn_lo := 3415403, cd_lo := 10000000}

private theorem tables : refined.checkTables = true := check_tables_427_1250

set_option maxHeartbeats 4000000
set_option Elab.async false

private theorem slice0 : refined.checkModelsSlice 0 40 = true := Eq.refl true
private theorem slice40 : refined.checkModelsSlice 40 40 = true := Eq.refl true
private theorem slice80 : refined.checkModelsSlice 80 40 = true := Eq.refl true
private theorem slice120 : refined.checkModelsSlice 120 40 = true := Eq.refl true
private theorem slice160 : refined.checkModelsSlice 160 40 = true := Eq.refl true
private theorem slice200 : refined.checkModelsSlice 200 40 = true := Eq.refl true
private theorem slice240 : refined.checkModelsSlice 240 40 = true := Eq.refl true
private theorem slice280 : refined.checkModelsSlice 280 37 = true := Eq.refl true

private theorem models : refined.checkModelsSlice 0 317 = true := by
  refine refined.checkModelsSlice_of_forall fun i hi => ?_
  by_cases h0 : i < 40
  · exact refined.of_checkModelsSlice slice0 (by omega) h0
  by_cases h40 : i < 80
  · exact refined.of_checkModelsSlice slice40 (by omega) h40
  by_cases h80 : i < 120
  · exact refined.of_checkModelsSlice slice80 (by omega) h80
  by_cases h120 : i < 160
  · exact refined.of_checkModelsSlice slice120 (by omega) h120
  by_cases h160 : i < 200
  · exact refined.of_checkModelsSlice slice160 (by omega) h160
  by_cases h200 : i < 240
  · exact refined.of_checkModelsSlice slice200 (by omega) h200
  by_cases h240 : i < 280
  · exact refined.of_checkModelsSlice slice240 (by omega) h240
  exact refined.of_checkModelsSlice slice280 (by omega) hi

@[expose] public section

/-- The same five-vertex dual coefficients have strictly negative slack at 0.3415403. -/
theorem hasCycleLe3_of_minOutDeg_ge_3415403_10000000
    {W : Type*} [Fintype W] [Nonempty W] (G : Digraph W) [DecidableRel G.adj]
    (hdeg : ∀ v, (3415403 / 10000000 : ℝ) * Fintype.card W ≤ (G.outDeg v : ℝ)) :
    G.HasCycleLe3 :=
  refined.hasCycleLe3 cStar_le_689_2000 tables models G hdeg

theorem cStar_le_3415403_10000000 : cStar ≤ (3415403 / 10000000 : ℝ) :=
  cStar_le_of_hasCycleLe3 hasCycleLe3_of_minOutDeg_ge_3415403_10000000

end

end CaccettaHaggkvist
