module

public import CaccettaHaggkvist.SixVertexProgram
public import CaccettaHaggkvist.CanonModels
public import CaccettaHaggkvist.SixVertexTables
public import Mathlib.Order.Fin.Basic

/-! # Reflection for six-vertex dual certificates

The permutation enumeration has 720 elements. Validity and strict ordering
of their six digits certify bijectivity. Each model slice checks the signed,
denominator-cleared inequalities for the same program used by the mean proof.
-/

@[expose] public section

namespace CaccettaHaggkvist.SixVertex

def permutationAt (table i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight table (Nat.mul 18 i)) 262143

def permutationKey (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.add (Nat.mul 8 (permutationKey p n)) (pDigit p n)

def checkPermutations (table : ℕ) : Bool :=
  allBelow 720 (fun i => validPerm 6 (permutationAt table i)) &&
  allBelow 719 (fun i => natLtBool (permutationKey (permutationAt table i) 6)
    (permutationKey (permutationAt table (Nat.succ i)) 6))

/-- The 720 lexicographic orderings in consecutive eighteen-bit fields. -/
def permutationTable : ℕ := 0x539484e508b9502e52839510e505a9486a50ca9582a52c29590a50999506650d19584654c195a0652989516252d09594254c895a22505474851d08c75031d28475111d06274889d10a76029d30276109d0a175085d11176045d50176205d2a075181d31076141d50876221d05c5487150cc5583152c45591150635488d510b5602d53035610d50e15588551195606557015630552e055981531856161570856321509c35070d0d435850d4c435a10d0a33508cd1133604cd5033620cd0e235888d11a36068d70236308d4e035a80d51836260d71036340d29c1517052d41595054cc15a3052a31518c53131614c550b1622c52e215988531a16168570a1632854e115a845519162645711163445053b084ec08bb102ec283b110ec05ab086ac0cab182ac2c2b190ac099b1066c0d1b1846c4c1b1a06c298b1162c2d0b1942c4c8b1a22c05570855c08d71035c28571115c06a708a9c14a72829c34272909c0a9710a5c15172845c54172a05c2a8711a1c35072941c54872a21c05d5087540cd5183542c551915406b508ad414b5282d43435290d40e9518a5415952865474152b0542e8519a1435852961474852b21409d31074c0d531854c4c531a14c0ab310acc1533284cc54332a0cc0ea318a8c15a32868c74232b08c4e831aa0c55832a60c75032b40c29d1117442d51195444cd11a3442ab111ac43531294c454b12a2c42ea119a8435a12968474a12b2844e911aa4455912a64475112b444054ac852b08cad032b284ad112b062ac88ab10aae02ab302ae10ab0a1ad086b111ae046b501ae206b2a0ad182b310ae142b508ae222b0558c856308d8d03632858d116306a8c8aa314a8e82a33428e90a30a98d0a631518e84635418ea0632a88d1a233508e94235488ea2230654c895310d4e03533054e115306c4c8b1314c4e83133444e91131294e0a531614e88539414ec0533284e1a133604e98139484ec2130a52d094b1152e054b5052e214b0ac2d0b0b1542e850b5442ea10b12a2e0a8b1622e888b9422ec08b5282e2a0b5602ea80b9502ec40b2a50d19433150e154350d0e23432ac0d1b033540e950354c0ea30332a0e1a833620e988394a0ec2835290e2a435610ea8439510ec44305ca8872a0cca9832a2c4a9912a063a888ea10baa02ea303aa10ea0e1a9886a119aa066a701aa306a2e0a9982a318aa162a708aa322a05d8887620cd8983622c589916206b888ae214b8a82e23438a90e20e9898a621598a86627418ab0622e8899a223588a96227488ab22206568895a10d6a035a3056a115a06c688b1a14c6a831a3446a911a1296a0a5a1616a885a9416ac05a3286a1a1a3606a981a9486ac21a0e529894a11d2a074a7052a314a0ec298b0a15c2a870a7442ab10a12b2a0aca1632a88ca9432ac0ca7282a3a0a7602ab80a9582ac60a2e509994231d0a174270d0a33422ec099b0235c0a970274c0ab30232b0a1ac23630a98c294b0ac2c27290a3a427610ab8429590ac64209ca507290d4a585294c4a5a1290a3a508e9113a604e9503a620e90e2a588a911aa606a9702a630a94e0a5a829518a62629710a6342909d8507610d58585614c585a1610ab850ae11538684e154386a0e10ea858aa115a8686a174286b0a14e885aa2155886a62175086b4210a56509591156605595056621590ac650b1915466851954466a11912a660a9916266889994266c099528662a1956066a81995066c4190e545895111d4607517054631510ec458b1115c46871174446b11112b460ad11634688d194346c0d1728463a1176046b81195846c6114e505a94151d0627417150635414ec05ab0155c06a70175406b50152b062ac156306a8c195306c4c172a063a8176206b88195a06c68129ca117282d4a195284cca1a3282a3a118e8313a214e850ba222e82e2a198a831aa216a870aa232a84e1a1a868519a22668711a2346829d8117602d58195604cd81a3602ab811ae03538294e054b82a2e02ea819aa035a8296a074a82b2a04e981aa6055982a66075182b4602a561195831562155850d6223582ac611b1835462951854c62a31832a621a9836262989894a62c298529622a5856162a85895162c4582e541995031d42175070d4233502ec419b1035c42971074c42b31032b421ad03634298d094b42c2d0729423a5076142b85095942c6504e521a94851d2227487152235484ec21ab0855c22a70875422b50852b222ac856322a8c895322c4c872a223a8876222b88895a22c688

set_option maxHeartbeats 4000000 in
theorem permutationTable_checked : checkPermutations permutationTable = true := Eq.refl true

private theorem key_congr {a b : ℕ} (n : ℕ) (h : ∀ i < n, pDigit a i = pDigit b i) :
    permutationKey a n = permutationKey b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [permutationKey, permutationKey, ih (fun i hi => h i (by omega)), h n (by omega)]

def coord (table p : ℕ) (i : Fin 6) : Fin 6 :=
  ⟨pDigit (permutationAt table p) i.val % 6, Nat.mod_lt _ (by decide)⟩

private theorem enumeration {table : ℕ} (ht : checkPermutations table = true) :
    ∃ e : Fin 720 ≃ Equiv.Perm (Fin 6), ∀ p i, e p i = coord table p.val i := by
  unfold checkPermutations at ht
  simp only [Bool.and_eq_true] at ht
  let ok (p : Fin 720) := of_allBelow ht.1 p.isLt
  let which (p : Fin 720) := permOfValid (ok p)
  have strict : StrictMono (fun p : Fin 720 => permutationKey (permutationAt table p.val) 6) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact natLtBool_eq_true_iff.mp (of_allBelow ht.2 p.isLt)
  have inj : Function.Injective which := by
    intro i j he
    apply strict.injective
    apply key_congr
    intro v hv
    have h := congrArg (fun f : Equiv.Perm (Fin 6) => (f ⟨v,hv⟩).val) he
    simpa only [which, permOfValid_val] using h
  let e := Equiv.ofBijective which ((Fintype.bijective_iff_injective_and_card which).mpr
    ⟨inj, by simp [Fintype.card_perm]; decide⟩)
  refine ⟨e,fun p i => Fin.ext ?_⟩
  change (permOfValid (ok p) i).val = pDigit (permutationAt table p.val) i.val % 6
  rw [permOfValid_val, Nat.mod_eq_of_lt (pDigit_lt_of_validPerm (ok p) i)]

def sumRows (f : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => (0,0)
  | n+1 =>
    let a := sumRows f n
    let b := f n
    (Int.add a.1 b.1, Int.add a.2 b.2)

theorem sumRows_spec (f : ℕ → ℤ × ℤ) (n : ℕ) :
    (sumRows f n).1 = ∑ i : Fin n, (f i.val).1 ∧
    (sumRows f n).2 = ∑ i : Fin n, (f i.val).2 := by
  induction n with
  | zero => simp [sumRows]
  | succ n ih =>
    simp only [sumRows, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    exact ⟨congrArg (· + _) ih.1, congrArg (· + _) ih.2⟩

def modelRow (P : Program) (table mask : ℕ) : ℤ × ℤ :=
  sumRows (fun p => P.eval ((maskGraph 6 mask).pullback (coord table p))) 720

set_option maxRecDepth 4096 in
theorem modelRow_spec (P : Program) {table : ℕ} (ht : checkPermutations table = true)
    (mask : ℕ) (c : ℝ) :
    symPerm (fun K => atRatio (P.score K) c) (maskGraph 6 mask) = atRatio (modelRow P table mask) c := by
  obtain ⟨e, he⟩ := enumeration ht
  let row (p : ℕ) := P.eval ((maskGraph 6 mask).pullback (coord table p))
  have eqn (i : Fin 720) : P.score ((maskGraph 6 mask).relabel (e i)) = row i.val := by
    have hv : (e i : Fin 6 → Fin 6) = coord table i.val := funext (he i)
    unfold OrientedGraph.relabel
    rw [hv]
    unfold Program.score row
    congr 1
  unfold symPerm
  rw [← Equiv.sum_comp e]
  simp_rw [eqn]
  unfold atRatio
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change _ = ((sumRows row 720).1 : ℝ) + c * ((sumRows row 720).2 : ℝ)
  rw [(sumRows_spec row 720).1, (sumRows_spec row 720).2]
  push_cast
  rfl

structure Endpoints where
  loNum : ℕ
  loDen : ℕ
  hiNum : ℕ
  hiDen : ℕ

def Endpoints.accepts (E : Endpoints) (z : ℤ × ℤ) : Bool :=
  decide ((E.loDen : ℤ)*z.1 + (E.loNum : ℤ)*z.2 ≤ 0) &&
  decide ((E.hiDen : ℤ)*z.1 + (E.hiNum : ℤ)*z.2 < 0)

theorem Endpoints.correct (E : Endpoints) {z : ℤ × ℤ} (hl : 0 < E.loDen) (hh : 0 < E.hiDen)
    (h : E.accepts z = true) :
    atRatio z ((E.loNum : ℝ)/E.loDen) ≤ 0 ∧ atRatio z ((E.hiNum : ℝ)/E.hiDen) < 0 := by
  simp only [accepts, Bool.and_eq_true, decide_eq_true_eq] at h
  have a : (E.loDen : ℝ)*z.1 + (E.loNum : ℝ)*z.2 ≤ 0 := by exact_mod_cast h.1
  have b : (E.hiDen : ℝ)*z.1 + (E.hiNum : ℝ)*z.2 < 0 := by exact_mod_cast h.2
  have hl' : (0 : ℝ) < E.loDen := Nat.cast_pos.mpr hl
  have hh' : (0 : ℝ) < E.hiDen := Nat.cast_pos.mpr hh
  unfold atRatio
  constructor
  · field_simp; linarith
  · field_simp; linarith

def checkSlice (P : Program) (E : Endpoints) (table start length : ℕ) : Bool :=
  checkRange (fun i => E.accepts (modelRow P table (models6Tree.get i))) start length

end CaccettaHaggkvist.SixVertex
