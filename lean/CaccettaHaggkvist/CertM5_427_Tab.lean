module

public import CaccettaHaggkvist.IntervalM5Bridge
public import CaccettaHaggkvist.CertM5_427_Data

namespace CaccettaHaggkvist

set_option maxHeartbeats 4000000 in
private lemma check_tab_core_427 : cert_m5_427_1250.checkTablesNoQ3 = true := Eq.refl true

set_option maxHeartbeats 4000000 in
private lemma check_q3_s0 : cert_m5_427_1250.checkQ3Slice 0 7 = true := Eq.refl true
set_option maxHeartbeats 4000000 in
private lemma check_q3_s1 : cert_m5_427_1250.checkQ3Slice 7 7 = true := Eq.refl true
set_option maxHeartbeats 4000000 in
private lemma check_q3_s2 : cert_m5_427_1250.checkQ3Slice 14 7 = true := Eq.refl true
set_option maxHeartbeats 4000000 in
private lemma check_q3_s3 : cert_m5_427_1250.checkQ3Slice 21 6 = true := Eq.refl true

@[expose] public section

theorem check_tables_427_1250 : cert_m5_427_1250.checkTables = true := by
  refine cert_m5_427_1250.checkTables_of_parts check_tab_core_427 fun rc hrc => ?_
  by_cases h0 : rc < 7
  · exact cert_m5_427_1250.of_checkQ3Slice check_q3_s0 (by omega) h0
  by_cases h1 : rc < 14
  · exact cert_m5_427_1250.of_checkQ3Slice check_q3_s1 (by omega) h1
  by_cases h2 : rc < 21
  · exact cert_m5_427_1250.of_checkQ3Slice check_q3_s2 (by omega) h2
  exact cert_m5_427_1250.of_checkQ3Slice check_q3_s3 (by omega) (by omega)

end

end CaccettaHaggkvist
