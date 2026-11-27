module

public import CaccettaHaggkvist.IntervalM5Bridge
public import CaccettaHaggkvist.CertM5_427_Data

namespace CaccettaHaggkvist

set_option maxHeartbeats 4000000 in
private lemma check_m_a : cert_m5_427_1250.checkModelsSlice 160 40 = true := Eq.refl true

set_option maxHeartbeats 4000000 in
private lemma check_m_b : cert_m5_427_1250.checkModelsSlice 200 40 = true := Eq.refl true

@[expose] public section

theorem check_models_427_s2 {gi : ℕ} (hlo : 160 ≤ gi) (hhi : gi < 240) :
    let uB := cert_m5_427_1250.uBias
    let vB := cert_m5_427_1250.vBias
    let threshLo := Nat.mul 120 (Nat.add (Nat.mul cert_m5_427_1250.cd_lo uB) (Nat.mul cert_m5_427_1250.cn_lo vB))
    let threshHi := Nat.mul 120 (Nat.add (Nat.mul cert_m5_427_1250.cd_hi uB) (Nat.mul cert_m5_427_1250.cn_hi vB))
    let maxSumV := Nat.mul 240 vB
    let mask := models5Tree.get gi
    let sumU := sumRange (fun p => cert_m5_427_1250.evalPermU mask (cert_m5_427_1250.perms5Tree.get p)) 0 120
    let sumV := sumRange (fun p => cert_m5_427_1250.evalPermV mask (cert_m5_427_1250.perms5Tree.get p)) 0 120
    (natLtBool (Nat.add (Nat.mul cert_m5_427_1250.cd_lo sumU) (Nat.mul cert_m5_427_1250.cn_lo sumV)) threshLo &&
     natLtBool (Nat.add (Nat.mul cert_m5_427_1250.cd_hi sumU) (Nat.mul cert_m5_427_1250.cn_hi sumV)) threshHi &&
     Nat.ble sumV maxSumV) = true := by
  by_cases ha : gi < 200
  · exact cert_m5_427_1250.of_checkModelsSlice check_m_a hlo ha
  · exact cert_m5_427_1250.of_checkModelsSlice check_m_b (by omega) (by omega)

end

end CaccettaHaggkvist
