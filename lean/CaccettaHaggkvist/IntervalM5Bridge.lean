module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.WeightBridge
public import CaccettaHaggkvist.FlagCert
public import CaccettaHaggkvist.CSS
public import CaccettaHaggkvist.CSS56
public import CaccettaHaggkvist.ExtremalBridge
public import CaccettaHaggkvist.KernelCore
public import CaccettaHaggkvist.CanonStep2to5
public import CaccettaHaggkvist.VanillaCertBridge
public import CaccettaHaggkvist.ExpectationBridge

/-!
# Zero-Typeclass Pure-`Nat` Bridge for Two-Endpoint Interval Certificates (`m = 5`)

Connects `ExtremalBridge.hasCycleLe3_of_interval_certificate` and `ExpectationBridge` (Classes 1–4:
out-regularity, Flag-SOS, Linear Generalized Induction, and Linear Pointwise CSS) to 100%
zero-typeclass `Nat.*` + `cond` GMP evaluation over the 317 canonical `C₃`-free 5-vertex models.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

/-! ## Section 1: Dimension-Generic Zero-Typeclass Prefix Adjacency Predicates -/

def allInBool (mask x : ℕ) (v : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => allInBool mask x v k && adjBool mask (v k) x

def noOutBool (mask x : ℕ) (v : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => noOutBool mask x v k && !(adjBool mask x (v k))

def srcStarBool (mask x : ℕ) (v : ℕ → ℕ) (k : ℕ) : Bool :=
  noOutBool mask x v k && !(allInBool mask x v k)

def chiPairBool (mask x y : ℕ) (v : ℕ → ℕ) (k : ℕ) : Bool :=
  allInBool mask x v k && allInBool mask y v k && !(adjBool mask x y) && !(adjBool mask y x)

lemma allInBool_eq_true_iff {m mask x : ℕ} {σ : Equiv.Perm (Fin m)} {v : ℕ → ℕ}
    (hx : ∃ ix : Fin m, (σ ix).1 = x)
    (hv : ∀ j : Fin m, v j.1 = (σ j).1) :
    ∀ {k : ℕ} (hk : k ≤ m),
      allInBool mask x v k = true ↔
        ∀ i : Fin k, adjBool mask (σ ⟨i.1, by omega⟩).1 x = true
  | 0, _ => by simp [allInBool]
  | k + 1, hk => by
    have _ := hx
    simp only [allInBool, Bool.and_eq_true]
    rw [allInBool_eq_true_iff hx hv (by omega), hv ⟨k, by omega⟩]
    constructor
    · rintro ⟨hinit, hlast⟩ i
      refine Fin.lastCases ?_ ?_ i
      · exact hlast
      · intro j; exact hinit j
    · intro hall
      exact ⟨fun j => hall j.castSucc, hall (Fin.last k)⟩

lemma noOutBool_eq_true_iff {m mask x : ℕ} {σ : Equiv.Perm (Fin m)} {v : ℕ → ℕ}
    (hv : ∀ j : Fin m, v j.1 = (σ j).1) :
    ∀ {k : ℕ} (hk : k ≤ m),
      noOutBool mask x v k = true ↔
        ∀ i : Fin k, ¬ (adjBool mask x (σ ⟨i.1, by omega⟩).1 = true)
  | 0, _ => by simp [noOutBool]
  | k + 1, hk => by
    simp only [noOutBool, Bool.and_eq_true, Bool.not_eq_true']
    rw [noOutBool_eq_true_iff hv (by omega), hv ⟨k, by omega⟩]
    constructor
    · rintro ⟨hinit, hlast⟩ i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.val_last]; rw [hlast]; decide
      · intro j; exact hinit j
    · intro hall
      refine ⟨fun j => hall j.castSucc, ?_⟩
      have hk_false := hall (Fin.last k)
      cases hb : adjBool mask x (σ ⟨k, by omega⟩).1
      · rfl
      · exact (hk_false hb).elim

lemma allInPred_relabel_iff {r mask : ℕ} (σ : Equiv.Perm (Fin (r + 1))) (v : ℕ → ℕ)
    (hv : ∀ j : Fin (r + 1), v j.1 = (σ j).1) {k_orig : ℕ} (hk : k_orig ≤ r) :
    allInPred k_orig hk ((maskGraph (r + 1) mask).relabel σ) ↔
      allInBool mask (v r) v k_orig = true := by
  have hlast : v r = (σ (Fin.last r)).1 := hv (Fin.last r)
  rw [hlast, allInBool_eq_true_iff ⟨Fin.last r, rfl⟩ hv (by omega)]
  rfl

lemma srcStarPred_relabel_iff {r mask : ℕ} (σ : Equiv.Perm (Fin (r + 1))) (v : ℕ → ℕ)
    (hv : ∀ j : Fin (r + 1), v j.1 = (σ j).1) {k_orig : ℕ} (hk : k_orig ≤ r) :
    srcStarPred k_orig hk ((maskGraph (r + 1) mask).relabel σ) ↔
      srcStarBool mask (v r) v k_orig = true := by
  unfold srcStarPred srcStarBool
  rw [allInPred_relabel_iff σ v hv hk]
  have hlast : v r = (σ (Fin.last r)).1 := hv (Fin.last r)
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  rw [hlast, noOutBool_eq_true_iff hv (by omega)]
  refine and_congr Iff.rfl ?_
  cases allInBool mask (σ (Fin.last r)).1 v k_orig <;> simp

lemma chiPred2_relabel_iff {r mask : ℕ} (σ : Equiv.Perm (Fin (r + 2))) (v : ℕ → ℕ)
    (hv : ∀ j : Fin (r + 2), v j.1 = (σ j).1) {k_orig : ℕ} (hk : k_orig ≤ r) :
    chiPred2 k_orig hk ((maskGraph (r + 2) mask).relabel σ) ↔
      chiPairBool mask (v r) (v (r + 1)) v k_orig = true := by
  unfold chiPred2 chiPairBool
  have hr : v r = (σ ⟨r, by omega⟩).1 := hv ⟨r, by omega⟩
  have hr1 : v (r + 1) = (σ ⟨r + 1, by omega⟩).1 := hv ⟨r + 1, by omega⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', and_assoc]
  rw [hr, hr1,
    allInBool_eq_true_iff ⟨⟨r, by omega⟩, rfl⟩ hv (by omega),
    allInBool_eq_true_iff ⟨⟨r + 1, by omega⟩, rfl⟩ hv (by omega)]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · change ¬ (adjBool mask (σ ⟨r, _⟩).1 (σ ⟨r + 1, _⟩).1 = true) ↔ _
    cases adjBool mask (σ ⟨r, by omega⟩).1 (σ ⟨r + 1, by omega⟩).1 <;> simp
  · change ¬ (adjBool mask (σ ⟨r + 1, _⟩).1 (σ ⟨r, _⟩).1 = true) ↔ _
    cases adjBool mask (σ ⟨r + 1, by omega⟩).1 (σ ⟨r, by omega⟩).1 <;> simp

lemma srcStarPred2_relabel_iff {r mask : ℕ} (σ : Equiv.Perm (Fin (r + 2))) (v : ℕ → ℕ)
    (hv : ∀ j : Fin (r + 2), v j.1 = (σ j).1) {k_orig : ℕ} (hk : k_orig ≤ r) :
    srcStarPred2 k_orig hk ((maskGraph (r + 2) mask).relabel σ) ↔
      srcStarBool mask (v r) v k_orig = true := by
  unfold srcStarPred2 srcStarBool
  have hr : v r = (σ ⟨r, by omega⟩).1 := hv ⟨r, by omega⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  rw [hr, noOutBool_eq_true_iff hv (by omega)]
  refine and_congr Iff.rfl ?_
  have hall := allInBool_eq_true_iff (mask := mask) ⟨⟨r, by omega⟩, rfl⟩ hv (k := k_orig) (by omega)
  cases hb : allInBool mask (σ ⟨r, by omega⟩).1 v k_orig
  · rw [hb] at hall
    simp only [Bool.false_eq_true, false_iff] at hall
    exact ⟨fun _ => rfl, fun _ => hall⟩
  · rw [hb] at hall
    simp only [true_iff] at hall
    exact ⟨fun h => (h hall).elim, fun h => Bool.noConfusion h⟩

/-! ## Section 2: Tangent Lists for Linear CSS & Exact Pre-Summed Coefficient Tables -/

structure CssTangentSpec where
  rn : ℕ
  rd : ℕ
  cssTree : NTree

noncomputable def evalCssListU {r : ℕ} (isTier2 : Bool) (k_orig : ℕ) (hk : k_orig ≤ r) :
    List CssTangentSpec → OrientedGraph (Fin (r + 2)) → ℝ
  | [], _ => 0
  | t :: rest, K =>
    linCssU isTier2 k_orig hk t.rn t.rd t.cssTree K + evalCssListU isTier2 k_orig hk rest K

noncomputable def evalCssListV {r : ℕ} (isTier2 : Bool) (k_orig : ℕ) (hk : k_orig ≤ r) :
    List CssTangentSpec → OrientedGraph (Fin (r + 2)) → ℝ
  | [], _ => 0
  | t :: rest, K =>
    linCssV isTier2 k_orig hk t.rn t.rd t.cssTree K + evalCssListV isTier2 k_orig hk rest K

def checkCssTangentList (k_orig r : ℕ) : List CssTangentSpec → Bool
  | [] => true
  | t :: rest =>
    natLtBool 0 t.rd && checkCssTree k_orig r t.cssTree && checkCssTangentList k_orig r rest

lemma expect_evalCssList_nonneg {n r k_orig : ℕ} (hn : 0 < n) (isTier2 : Bool)
    (hk : k_orig ≤ r) (hk_bdd : k_orig ≤ 2 ^ 17)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree) {c₀ : ℝ}
    (hreg : ∀ u : Fin n, G₀.toDigraph.outWeight (unifWeight (Fin n)) u = c₀) :
    ∀ {ts : List CssTangentSpec}, checkCssTangentList k_orig r ts = true →
      0 ≤ ∑ z : Fin (r + 2) → Fin n,
        tupleWeight (unifWeight (Fin n)) z *
          (evalCssListU isTier2 k_orig hk ts (G₀.pullback z) +
            c₀ * evalCssListV isTier2 k_orig hk ts (G₀.pullback z))
  | [], _ => by simp [evalCssListU, evalCssListV]
  | t :: rest, hchk => by
    unfold checkCssTangentList at hchk
    simp only [Bool.and_eq_true, natLtBool_eq_true_iff] at hchk
    rcases hchk with ⟨⟨hrd, htree⟩, hrest⟩
    have hsplit : ∀ z : Fin (r + 2) → Fin n,
        tupleWeight (unifWeight (Fin n)) z *
          (evalCssListU isTier2 k_orig hk (t :: rest) (G₀.pullback z) +
            c₀ * evalCssListV isTier2 k_orig hk (t :: rest) (G₀.pullback z)) =
        tupleWeight (unifWeight (Fin n)) z *
          (linCssU isTier2 k_orig hk t.rn t.rd t.cssTree (G₀.pullback z) +
            c₀ * linCssV isTier2 k_orig hk t.rn t.rd t.cssTree (G₀.pullback z)) +
        tupleWeight (unifWeight (Fin n)) z *
          (evalCssListU isTier2 k_orig hk rest (G₀.pullback z) +
            c₀ * evalCssListV isTier2 k_orig hk rest (G₀.pullback z)) :=
      fun z => by simp only [evalCssListU, evalCssListV]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    exact add_nonneg
      (expect_linCss_nonneg hn hrd isTier2 hk hk_bdd htree G₀ hG₀ hreg)
      (expect_evalCssList_nonneg hn isTier2 hk hk_bdd G₀ hG₀ hreg hrest)

def sumCssChi (isTier2 : Bool) : List CssTangentSpec → ℕ → ℕ
  | [], _ => 0
  | t :: rest, c =>
    let a_num := cond isTier2 5 1
    Nat.add (Nat.mul (t.cssTree.get c) (Nat.mul a_num (Nat.mul t.rd t.rd)))
      (sumCssChi isTier2 rest c)

def sumCssSs (isTier2 : Bool) : List CssTangentSpec → ℕ → ℕ
  | [], _ => 0
  | t :: rest, c =>
    let a_den := cond isTier2 6 1
    Nat.add (Nat.mul (t.cssTree.get c) (Nat.mul (Nat.mul 2 a_den) (Nat.mul t.rn t.rd)))
      (sumCssSs isTier2 rest c)

def sumCssU1 (isTier2 : Bool) : List CssTangentSpec → ℕ → ℕ
  | [], _ => 0
  | t :: rest, c =>
    let a_den := cond isTier2 6 1
    Nat.add (Nat.mul (t.cssTree.get c) (Nat.mul a_den (Nat.mul t.rn t.rn)))
      (sumCssU1 isTier2 rest c)

lemma evalCssListU_eq_sums {r : ℕ} (isTier2 : Bool) (k_orig : ℕ) (hk : k_orig ≤ r)
    (ts : List CssTangentSpec) (K : OrientedGraph (Fin (r + 2))) :
    let c := graphTritCode (K.pullback embInit2)
    evalCssListU isTier2 k_orig hk ts K =
      (sumCssChi isTier2 ts c : ℝ) * (@ite ℝ (chiPred2 k_orig hk K) (Classical.propDecidable _) 1 0) +
      (sumCssSs isTier2 ts c : ℝ) * (@ite ℝ (srcStarPred2 k_orig hk K) (Classical.propDecidable _) 1 0) +
      (sumCssU1 isTier2 ts c : ℝ) := by
  induction ts with
  | nil => simp [evalCssListU, sumCssChi, sumCssSs, sumCssU1]
  | cons t rest ih =>
    simp only [evalCssListU, sumCssChi, sumCssSs, sumCssU1, natAdd_eq, natMul_eq]
    rw [ih]
    unfold linCssU
    cases isTier2 <;> simp only [Bool.cond_false, Bool.cond_true, ↓reduceIte] <;> push_cast <;> ring

lemma evalCssListV_eq_sum {r : ℕ} (isTier2 : Bool) (k_orig : ℕ) (hk : k_orig ≤ r)
    (ts : List CssTangentSpec) (K : OrientedGraph (Fin (r + 2))) :
    evalCssListV isTier2 k_orig hk ts K = -(sumCssSs isTier2 ts (graphTritCode (K.pullback embInit2)) : ℝ) := by
  induction ts with
  | nil => simp [evalCssListV, sumCssSs]
  | cons t rest ih =>
    simp only [evalCssListV, sumCssSs, natAdd_eq, natMul_eq]
    rw [ih]
    unfold linCssV
    cases isTier2 <;> simp only [Bool.cond_false, Bool.cond_true, ↓reduceIte] <;> push_cast <;> ring

/-! ## Section 3: Complete `IntervalM5Cert` Package & Pure-`Nat` Verifier -/

structure IntervalM5Cert where
  cn_lo : ℕ
  cd_lo : ℕ
  cn_hi : ℕ
  cd_hi : ℕ
  isTier2 : Bool
  lamOff : ℕ
  lamTree : NTree
  q0Off : ℕ
  q0Tree : NTree
  q3Off : ℕ
  q3Tree : NTree
  facs1 : List SosFacSpec
  facs3 : List SosFacSpec
  m1_bdd : ℕ
  ind1Tree : NTree
  m2_bdd : ℕ
  ind2Tree : NTree
  m3_bdd : ℕ
  ind3Tree : NTree
  m4_bdd : ℕ
  ind4Tree : NTree
  css1 : List CssTangentSpec
  css2 : List CssTangentSpec
  css3 : List CssTangentSpec
  chi1Tree : NTree
  chi2Tree : NTree
  chi3Tree : NTree
  ss1Tree : NTree
  ss2Tree : NTree
  ss3Tree : NTree
  cssU1Tree : NTree
  cssV1Tree : NTree
  cssV1Max : ℕ
  perms5Tree : NTree

noncomputable def IntervalM5Cert.U_fn (C : IntervalM5Cert) (K : OrientedGraph (Fin 5)) : ℝ :=
  degAffineU (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) K +
  evalSosList (k := 1) (d := 2) C.facs1 K +
  evalSosList (k := 3) (d := 1) C.facs3 K +
  linIndU 1 (by decide) C.ind1Tree K +
  linIndU 2 (by decide) C.ind2Tree K +
  linIndU 3 (by decide) C.ind3Tree K +
  linIndU 4 (by decide) C.ind4Tree K +
  evalCssListU C.isTier2 1 (by decide) C.css1 K +
  evalCssListU C.isTier2 2 (by decide) C.css2 K +
  evalCssListU C.isTier2 3 (by decide) C.css3 K

noncomputable def IntervalM5Cert.V_fn (C : IntervalM5Cert) (K : OrientedGraph (Fin 5)) : ℝ :=
  degAffineV (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) K +
  linIndV 1 (by decide) C.ind1Tree K +
  linIndV 2 (by decide) C.ind2Tree K +
  linIndV 3 (by decide) C.ind3Tree K +
  linIndV 4 (by decide) C.ind4Tree K +
  evalCssListV C.isTier2 1 (by decide) C.css1 K +
  evalCssListV C.isTier2 2 (by decide) C.css2 K +
  evalCssListV C.isTier2 3 (by decide) C.css3 K

def IntervalM5Cert.uBias (C : IntervalM5Cert) : ℕ :=
  Nat.add (Nat.add C.lamOff C.q0Off) C.q3Off

def IntervalM5Cert.vBias (C : IntervalM5Cert) : ℕ :=
  Nat.add
    (Nat.add (Nat.add (Nat.add C.lamOff C.m1_bdd) C.m2_bdd) (Nat.add C.m3_bdd C.m4_bdd))
    C.cssV1Max

def IntervalM5Cert.checkTables (C : IntervalM5Cert) : Bool :=
  natLtBool 0 C.cd_lo &&
  natLtBool 0 C.cd_hi &&
  Nat.ble (Nat.mul C.cn_lo C.cd_hi) (Nat.mul C.cn_hi C.cd_lo) &&
  checkPerms5 C.perms5Tree &&
  allBelow 729 (fun c4 => Nat.ble (C.lamTree.get c4) (Nat.mul 2 C.lamOff)) &&
  allBelow 27 (fun lc =>
    allBelow 27 (fun rc =>
      let pn := sosListPosNeg C.facs1 0 lc rc
      Nat.beq (Nat.add (C.q0Tree.get (Nat.add (Nat.mul lc 27) rc)) pn.2)
        (Nat.add C.q0Off pn.1))) &&
  allBelow 27 (fun rc =>
    let facs_rc := filterFacs rc C.facs3
    allBelow 27 (fun rowL =>
      allBelow 27 (fun rowR =>
        let lc := Nat.add rowL (Nat.mul 27 rc)
        let rgc := Nat.add rowR (Nat.mul 27 rc)
        let pn := sosListPosNeg facs_rc rc lc rgc
        Nat.beq (Nat.add (C.q3Tree.get (Nat.add (Nat.add (Nat.mul rc 729) (Nat.mul rowL 27)) rowR)) pn.2)
          (Nat.add C.q3Off pn.1)))) &&
  checkIndTree 1 4 C.m1_bdd C.ind1Tree &&
  checkIndTree 2 4 C.m2_bdd C.ind2Tree &&
  checkIndTree 3 4 C.m3_bdd C.ind3Tree &&
  checkIndTree 4 4 C.m4_bdd C.ind4Tree &&
  checkCssTangentList 1 3 C.css1 &&
  checkCssTangentList 2 3 C.css2 &&
  checkCssTangentList 3 3 C.css3 &&
  allBelow 27 (fun c3 =>
    Nat.beq (C.chi1Tree.get c3) (sumCssChi C.isTier2 C.css1 c3) &&
    Nat.beq (C.chi2Tree.get c3) (sumCssChi C.isTier2 C.css2 c3) &&
    Nat.beq (C.chi3Tree.get c3) (sumCssChi C.isTier2 C.css3 c3) &&
    Nat.beq (C.ss1Tree.get c3) (sumCssSs C.isTier2 C.css1 c3) &&
    Nat.beq (C.ss2Tree.get c3) (sumCssSs C.isTier2 C.css2 c3) &&
    Nat.beq (C.ss3Tree.get c3) (sumCssSs C.isTier2 C.css3 c3) &&
    Nat.beq (C.cssU1Tree.get c3)
      (Nat.add (Nat.add (sumCssU1 C.isTier2 C.css1 c3) (sumCssU1 C.isTier2 C.css2 c3))
        (sumCssU1 C.isTier2 C.css3 c3)) &&
    Nat.beq (C.cssV1Tree.get c3)
      (Nat.add (Nat.add (sumCssSs C.isTier2 C.css1 c3) (sumCssSs C.isTier2 C.css2 c3))
        (sumCssSs C.isTier2 C.css3 c3)) &&
    Nat.ble (C.cssV1Tree.get c3) C.cssV1Max)

lemma IntervalM5Cert.checkPerms5_of_checkTables {C : IntervalM5Cert} (htab : C.checkTables = true) :
    checkPerms5 C.perms5Tree = true := by
  unfold IntervalM5Cert.checkTables at htab
  simp only [Bool.and_eq_true] at htab
  exact htab.1.1.1.1.1.1.1.1.1.1.1.2

def IntervalM5Cert.checkQ3At (C : IntervalM5Cert) (rc : ℕ) : Bool :=
  let facs_rc := filterFacs rc C.facs3
  allBelow 27 (fun rowL =>
    allBelow 27 (fun rowR =>
      let lc := Nat.add rowL (Nat.mul 27 rc)
      let rgc := Nat.add rowR (Nat.mul 27 rc)
      let pn := sosListPosNeg facs_rc rc lc rgc
      Nat.beq (Nat.add (C.q3Tree.get (Nat.add (Nat.add (Nat.mul rc 729) (Nat.mul rowL 27)) rowR)) pn.2)
        (Nat.add C.q3Off pn.1)))

def IntervalM5Cert.checkQ3Slice (C : IntervalM5Cert) (lo len : ℕ) : Bool :=
  checkRange C.checkQ3At lo len

def IntervalM5Cert.checkTablesNoQ3 (C : IntervalM5Cert) : Bool :=
  natLtBool 0 C.cd_lo &&
  natLtBool 0 C.cd_hi &&
  Nat.ble (Nat.mul C.cn_lo C.cd_hi) (Nat.mul C.cn_hi C.cd_lo) &&
  checkPerms5 C.perms5Tree &&
  allBelow 729 (fun c4 => Nat.ble (C.lamTree.get c4) (Nat.mul 2 C.lamOff)) &&
  allBelow 27 (fun lc =>
    allBelow 27 (fun rc =>
      let pn := sosListPosNeg C.facs1 0 lc rc
      Nat.beq (Nat.add (C.q0Tree.get (Nat.add (Nat.mul lc 27) rc)) pn.2)
        (Nat.add C.q0Off pn.1))) &&
  checkIndTree 1 4 C.m1_bdd C.ind1Tree &&
  checkIndTree 2 4 C.m2_bdd C.ind2Tree &&
  checkIndTree 3 4 C.m3_bdd C.ind3Tree &&
  checkIndTree 4 4 C.m4_bdd C.ind4Tree &&
  checkCssTangentList 1 3 C.css1 &&
  checkCssTangentList 2 3 C.css2 &&
  checkCssTangentList 3 3 C.css3 &&
  allBelow 27 (fun c3 =>
    Nat.beq (C.chi1Tree.get c3) (sumCssChi C.isTier2 C.css1 c3) &&
    Nat.beq (C.chi2Tree.get c3) (sumCssChi C.isTier2 C.css2 c3) &&
    Nat.beq (C.chi3Tree.get c3) (sumCssChi C.isTier2 C.css3 c3) &&
    Nat.beq (C.ss1Tree.get c3) (sumCssSs C.isTier2 C.css1 c3) &&
    Nat.beq (C.ss2Tree.get c3) (sumCssSs C.isTier2 C.css2 c3) &&
    Nat.beq (C.ss3Tree.get c3) (sumCssSs C.isTier2 C.css3 c3) &&
    Nat.beq (C.cssU1Tree.get c3)
      (Nat.add (Nat.add (sumCssU1 C.isTier2 C.css1 c3) (sumCssU1 C.isTier2 C.css2 c3))
        (sumCssU1 C.isTier2 C.css3 c3)) &&
    Nat.beq (C.cssV1Tree.get c3)
      (Nat.add (Nat.add (sumCssSs C.isTier2 C.css1 c3) (sumCssSs C.isTier2 C.css2 c3))
        (sumCssSs C.isTier2 C.css3 c3)) &&
    Nat.ble (C.cssV1Tree.get c3) C.cssV1Max)

lemma IntervalM5Cert.checkTables_of_parts {C : IntervalM5Cert}
    (hcore : C.checkTablesNoQ3 = true)
    (hq3 : ∀ rc < 27, C.checkQ3At rc = true) :
    C.checkTables = true := by
  unfold IntervalM5Cert.checkTables IntervalM5Cert.checkTablesNoQ3 at *
  simp only [Bool.and_eq_true] at hcore ⊢
  rcases hcore with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, allBelow_eq_true_of_forall (by norm_num) hq3⟩,
    h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩

lemma IntervalM5Cert.of_checkQ3Slice {C : IntervalM5Cert} {lo len rc : ℕ}
    (h : C.checkQ3Slice lo len = true) (hlo : lo ≤ rc) (hhi : rc < lo + len) :
    C.checkQ3At rc = true :=
  of_checkRange h hlo hhi

def IntervalM5Cert.evalPermU (C : IntervalM5Cert) (mask pCode : ℕ) : ℕ :=
  let v0 := pDigit pCode 0
  let v1 := pDigit pCode 1
  let v2 := pDigit pCode 2
  let v3 := pDigit pCode 3
  let v4 := pDigit pCode 4
  let vAll : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) v0
      (cond (Nat.beq i 1) v1
        (cond (Nat.beq i 2) v2 (cond (Nat.beq i 3) v3 v4)))
  let vSkip : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v2 (cond (Nat.beq i 2) v3 v4))
  let c4_skip := maskSubTritCode mask vSkip 4
  let lv := C.lamTree.get c4_skip
  let uDeg := cond (adjBool mask v0 v1) lv C.lamOff
  let vL0 : ℕ → ℕ := fun i => cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v1 v2)
  let vR0 : ℕ → ℕ := fun i => cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v3 v4)
  let lc0 := maskSubTritCode mask vL0 3
  let rc0 := maskSubTritCode mask vR0 3
  let q0Nat := C.q0Tree.get (Nat.add (Nat.mul lc0 27) rc0)
  let rowL := packRowTrits mask v3 vL0 0 3
  let rowR := packRowTrits mask v4 vL0 0 3
  let q3Nat := C.q3Tree.get (Nat.add (Nat.add (Nat.mul lc0 729) (Nat.mul rowL 27)) rowR)
  let c4_init := Nat.add rowL (Nat.mul 27 lc0)
  let uInd :=
    Nat.add
      (Nat.add
        (cond (srcStarBool mask v4 vAll 1) (C.ind1Tree.get c4_init) 0)
        (cond (srcStarBool mask v4 vAll 2) (C.ind2Tree.get c4_init) 0))
      (Nat.add
        (cond (srcStarBool mask v4 vAll 3) (C.ind3Tree.get c4_init) 0)
        (cond (srcStarBool mask v4 vAll 4) (C.ind4Tree.get c4_init) 0))
  let uCss :=
    Nat.add
      (Nat.add
        (Nat.add
          (cond (chiPairBool mask v3 v4 vAll 1) (C.chi1Tree.get lc0) 0)
          (cond (chiPairBool mask v3 v4 vAll 2) (C.chi2Tree.get lc0) 0))
        (Nat.add
          (cond (chiPairBool mask v3 v4 vAll 3) (C.chi3Tree.get lc0) 0)
          (cond (srcStarBool mask v3 vAll 1) (C.ss1Tree.get lc0) 0)))
      (Nat.add
        (Nat.add
          (cond (srcStarBool mask v3 vAll 2) (C.ss2Tree.get lc0) 0)
          (cond (srcStarBool mask v3 vAll 3) (C.ss3Tree.get lc0) 0))
        (C.cssU1Tree.get lc0))
  Nat.add (Nat.add (Nat.add uDeg q0Nat) q3Nat) (Nat.add uInd uCss)

def IntervalM5Cert.evalPermV (C : IntervalM5Cert) (mask pCode : ℕ) : ℕ :=
  let v0 := pDigit pCode 0
  let v1 := pDigit pCode 1
  let v2 := pDigit pCode 2
  let v3 := pDigit pCode 3
  let v4 := pDigit pCode 4
  let vAll : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) v0
      (cond (Nat.beq i 1) v1
        (cond (Nat.beq i 2) v2 (cond (Nat.beq i 3) v3 v4)))
  let vSkip : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v2 (cond (Nat.beq i 2) v3 v4))
  let c4_skip := maskSubTritCode mask vSkip 4
  let vDeg := Nat.sub (Nat.mul 2 C.lamOff) (C.lamTree.get c4_skip)
  let vL0 : ℕ → ℕ := fun i => cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v1 v2)
  let lc0 := maskSubTritCode mask vL0 3
  let rowL := packRowTrits mask v3 vL0 0 3
  let c4_init := Nat.add rowL (Nat.mul 27 lc0)
  let vInd :=
    Nat.add
      (Nat.add
        (cond (allInBool mask v4 vAll 1) C.m1_bdd (Nat.sub C.m1_bdd (C.ind1Tree.get c4_init)))
        (cond (allInBool mask v4 vAll 2) C.m2_bdd (Nat.sub C.m2_bdd (C.ind2Tree.get c4_init))))
      (Nat.add
        (cond (allInBool mask v4 vAll 3) C.m3_bdd (Nat.sub C.m3_bdd (C.ind3Tree.get c4_init)))
        (cond (allInBool mask v4 vAll 4) C.m4_bdd (Nat.sub C.m4_bdd (C.ind4Tree.get c4_init))))
  let vCss := Nat.sub C.cssV1Max (C.cssV1Tree.get lc0)
  Nat.add (Nat.add vDeg vInd) vCss

def IntervalM5Cert.checkModelsSlice (C : IntervalM5Cert) (offset len : ℕ) : Bool :=
  let uB := C.uBias
  let vB := C.vBias
  let threshLo := Nat.mul 120 (Nat.add (Nat.mul C.cd_lo uB) (Nat.mul C.cn_lo vB))
  let threshHi := Nat.mul 120 (Nat.add (Nat.mul C.cd_hi uB) (Nat.mul C.cn_hi vB))
  let maxSumV := Nat.mul 240 vB
  allBelow len (fun localIdx =>
    let mask := models5Tree.get (Nat.add offset localIdx)
    let sumU := sumRange (fun p => C.evalPermU mask (C.perms5Tree.get p)) 0 120
    let sumV := sumRange (fun p => C.evalPermV mask (C.perms5Tree.get p)) 0 120
    natLtBool (Nat.add (Nat.mul C.cd_lo sumU) (Nat.mul C.cn_lo sumV)) threshLo &&
    natLtBool (Nat.add (Nat.mul C.cd_hi sumU) (Nat.mul C.cn_hi sumV)) threshHi &&
    Nat.ble sumV maxSumV)

lemma IntervalM5Cert.of_checkModelsSlice {C : IntervalM5Cert} {offset len gi : ℕ}
    (h : C.checkModelsSlice offset len = true) (hlo : offset ≤ gi) (hhi : gi < offset + len) :
    let uB := C.uBias
    let vB := C.vBias
    let threshLo := Nat.mul 120 (Nat.add (Nat.mul C.cd_lo uB) (Nat.mul C.cn_lo vB))
    let threshHi := Nat.mul 120 (Nat.add (Nat.mul C.cd_hi uB) (Nat.mul C.cn_hi vB))
    let maxSumV := Nat.mul 240 vB
    let mask := models5Tree.get gi
    let sumU := sumRange (fun p => C.evalPermU mask (C.perms5Tree.get p)) 0 120
    let sumV := sumRange (fun p => C.evalPermV mask (C.perms5Tree.get p)) 0 120
    (natLtBool (Nat.add (Nat.mul C.cd_lo sumU) (Nat.mul C.cn_lo sumV)) threshLo &&
     natLtBool (Nat.add (Nat.mul C.cd_hi sumU) (Nat.mul C.cn_hi sumV)) threshHi &&
     Nat.ble sumV maxSumV) = true := by
  unfold IntervalM5Cert.checkModelsSlice at h
  have h1 := of_allBelow h (i := gi - offset) (by omega)
  have heq : Nat.add offset (gi - offset) = gi := by change offset + (gi - offset) = gi; omega
  dsimp only at h1 ⊢
  rw [heq] at h1
  exact h1

lemma IntervalM5Cert.checkModelsSlice_of_forall {C : IntervalM5Cert}
    (hall : ∀ gi < 317,
      let uB := C.uBias
      let vB := C.vBias
      let threshLo := Nat.mul 120 (Nat.add (Nat.mul C.cd_lo uB) (Nat.mul C.cn_lo vB))
      let threshHi := Nat.mul 120 (Nat.add (Nat.mul C.cd_hi uB) (Nat.mul C.cn_hi vB))
      let maxSumV := Nat.mul 240 vB
      let mask := models5Tree.get gi
      let sumU := sumRange (fun p => C.evalPermU mask (C.perms5Tree.get p)) 0 120
      let sumV := sumRange (fun p => C.evalPermV mask (C.perms5Tree.get p)) 0 120
      (natLtBool (Nat.add (Nat.mul C.cd_lo sumU) (Nat.mul C.cn_lo sumV)) threshLo &&
       natLtBool (Nat.add (Nat.mul C.cd_hi sumU) (Nat.mul C.cn_hi sumV)) threshHi &&
       Nat.ble sumV maxSumV) = true) :
    C.checkModelsSlice 0 317 = true := by
  unfold IntervalM5Cert.checkModelsSlice
  refine allBelow_eq_true_of_forall (by norm_num) fun gi hgi => ?_
  simpa [natAdd_eq] using hall gi hgi

private lemma evalPermU_eq (C : IntervalM5Cert) (htab : C.checkTables = true)
    (mask : ℕ) (p : Fin 120) :
    (C.evalPermU mask (C.perms5Tree.get p.1) : ℝ) =
      (C.uBias : ℝ) +
        C.U_fn ((maskGraph 5 mask).relabel
          (permOfValid (validPerm_of_checkPerms5 (C.checkPerms5_of_checkTables htab) p))) := by
  let pCode := C.perms5Tree.get p.1
  let hpv := validPerm_of_checkPerms5 (C.checkPerms5_of_checkTables htab) p
  let σ := permOfValid hpv
  let K := (maskGraph 5 mask).relabel σ
  have htab' := htab
  unfold IntervalM5Cert.checkTables at htab'
  simp only [Bool.and_eq_true, natLtBool_eq_true_iff, Nat.ble_eq] at htab'
  rcases htab' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hq0_eq⟩, hq3_eq⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hcss27⟩
  let vAll : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 1)
        (cond (Nat.beq i 2) (pDigit pCode 2)
          (cond (Nat.beq i 3) (pDigit pCode 3) (pDigit pCode 4))))
  have hvAll : ∀ j : Fin 5, vAll j.1 = (σ j).1 := fun j => by
    fin_cases j <;> simp only [σ, permOfValid_val] <;> rfl
  let vSkip : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 2)
        (cond (Nat.beq i 2) (pDigit pCode 3) (pDigit pCode 4)))
  have hc4_skip_eq : graphTritCode (K.pullback embSkipOne) = maskSubTritCode mask vSkip 4 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embSkipOne) vSkip fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  let vL0 : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0) (cond (Nat.beq i 1) (pDigit pCode 1) (pDigit pCode 2))
  let vR0 : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0) (cond (Nat.beq i 1) (pDigit pCode 3) (pDigit pCode 4))
  have hlc0_eq : graphTritCode (K.pullback (embLeft (k := 1) (d := 2))) =
      maskSubTritCode mask vL0 3 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embLeft (k := 1) (d := 2)) vL0 fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  have hrc0_eq : graphTritCode (K.pullback (embRight (k := 1) (d := 2))) =
      maskSubTritCode mask vR0 3 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embRight (k := 1) (d := 2)) vR0 fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  have hroot1_eq : graphTritCode (K.pullback (embRoot (k := 1) (d := 2))) = 0 := by
    have hlt1 := graphTritCode_lt (K.pullback (embRoot (k := 1) (d := 2)))
    omega
  have hlc0_lt : maskSubTritCode mask vL0 3 < 27 := by rw [← hlc0_eq]; exact graphTritCode_lt _
  have hrc0_lt : maskSubTritCode mask vR0 3 < 27 := by rw [← hrc0_eq]; exact graphTritCode_lt _
  have hq0_cell := Nat.beq_eq.mp (of_allBelow (of_allBelow hq0_eq hlc0_lt) hrc0_lt)
  simp only [natAdd_eq, natMul_eq] at hq0_cell
  have hq0_real : (C.q0Tree.get (maskSubTritCode mask vL0 3 * 27 + maskSubTritCode mask vR0 3) : ℝ) =
      (C.q0Off : ℝ) + evalSosList (k := 1) (d := 2) C.facs1 K := by
    rw [sosListPosNeg_real (k := 1) (d := 2) C.facs1 K, hroot1_eq, hlc0_eq, hrc0_eq]
    have hcast : ((C.q0Tree.get (maskSubTritCode mask vL0 3 * 27 + maskSubTritCode mask vR0 3) +
        (sosListPosNeg C.facs1 0 (maskSubTritCode mask vL0 3) (maskSubTritCode mask vR0 3)).2 : ℕ) : ℝ) =
        ((C.q0Off + (sosListPosNeg C.facs1 0 (maskSubTritCode mask vL0 3) (maskSubTritCode mask vR0 3)).1 : ℕ) : ℝ) := by
      exact_mod_cast hq0_cell
    push_cast at hcast; linarith
  have hroot3_eq : graphTritCode (K.pullback (embRoot (k := 3) (d := 1))) =
      maskSubTritCode mask vL0 3 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embRoot (k := 3) (d := 1)) vL0 fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  have hembInit2_eq : graphTritCode (K.pullback (embInit2 (r := 3))) =
      maskSubTritCode mask vL0 3 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embInit2 (r := 3)) vL0 fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  let vL3 : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 1)
        (cond (Nat.beq i 2) (pDigit pCode 2) (pDigit pCode 3)))
  let vR3 : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 1)
        (cond (Nat.beq i 2) (pDigit pCode 2) (pDigit pCode 4)))
  have hlc3_eq : graphTritCode (K.pullback (embLeft (k := 3) (d := 1))) =
      packRowTrits mask (pDigit pCode 3) vL0 0 3 + 27 * maskSubTritCode mask vL0 3 :=
    graphTritCode_pullback_maskGraph mask (σ ∘ embLeft (k := 3) (d := 1)) vL3
      (fun i => by fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl)
  have hcastSucc_eq : graphTritCode (K.pullback Fin.castSucc) =
      packRowTrits mask (pDigit pCode 3) vL0 0 3 + 27 * maskSubTritCode mask vL0 3 :=
    graphTritCode_pullback_maskGraph mask (σ ∘ Fin.castSucc) vL3
      (fun i => by fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl)
  have hrc3_eq : graphTritCode (K.pullback (embRight (k := 3) (d := 1))) =
      packRowTrits mask (pDigit pCode 4) vL0 0 3 + 27 * maskSubTritCode mask vL0 3 :=
    graphTritCode_pullback_maskGraph mask (σ ∘ embRight (k := 3) (d := 1)) vR3
      (fun i => by fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl)
  let rowL := packRowTrits mask (pDigit pCode 3) vL0 0 3
  let rowR := packRowTrits mask (pDigit pCode 4) vL0 0 3
  have hrowL_lt : rowL < 27 := rowTrits_lt_27 mask (pDigit pCode 3) vL0
  have hrowR_lt : rowR < 27 := rowTrits_lt_27 mask (pDigit pCode 4) vL0
  have hq3_cell := Nat.beq_eq.mp (of_allBelow (of_allBelow (of_allBelow hq3_eq hlc0_lt) hrowL_lt) hrowR_lt)
  simp only [natAdd_eq, natMul_eq, sosListPosNeg_filterFacs] at hq3_cell
  have hq3_real : (C.q3Tree.get (maskSubTritCode mask vL0 3 * 729 + rowL * 27 + rowR) : ℝ) =
      (C.q3Off : ℝ) + evalSosList (k := 3) (d := 1) C.facs3 K := by
    rw [sosListPosNeg_real (k := 3) (d := 1) C.facs3 K, hroot3_eq, hlc3_eq, hrc3_eq]
    have hcast : ((C.q3Tree.get (maskSubTritCode mask vL0 3 * 729 + rowL * 27 + rowR) +
        (sosListPosNeg C.facs3 (maskSubTritCode mask vL0 3)
          (rowL + 27 * maskSubTritCode mask vL0 3)
          (rowR + 27 * maskSubTritCode mask vL0 3)).2 : ℕ) : ℝ) =
        ((C.q3Off + (sosListPosNeg C.facs3 (maskSubTritCode mask vL0 3)
          (rowL + 27 * maskSubTritCode mask vL0 3)
          (rowR + 27 * maskSubTritCode mask vL0 3)).1 : ℕ) : ℝ) := by
      exact_mod_cast hq3_cell
    push_cast at hcast; linarith
  -- DegAffineU
  have hadj01 : K.adj 0 1 ↔ adjBool mask (pDigit pCode 0) (pDigit pCode 1) = true := by
    change adjBool mask (σ 0).1 (σ 1).1 = true ↔ _
    simp [σ, pCode]
  have huDeg_real : ((cond (adjBool mask (pDigit pCode 0) (pDigit pCode 1))
      (C.lamTree.get (maskSubTritCode mask vSkip 4)) C.lamOff : ℕ) : ℝ) =
      (C.lamOff : ℝ) +
        degAffineU (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) K := by
    unfold degAffineU
    dsimp only
    rw [hc4_skip_eq]
    cases hb : adjBool mask (pDigit pCode 0) (pDigit pCode 1)
    · have hnk : ¬ K.adj 0 1 := fun h => by rw [hadj01.mp h] at hb; cases hb
      simp [hnk]
    · have hk : K.adj 0 1 := hadj01.mpr hb
      simp [hk]
  -- Helper converting (@ite ℝ P dec 1 0) when P ↔ b = true:
  have hite_cond : ∀ (P : Prop) (b : Bool) (val : ℕ), (P ↔ b = true) →
      ((cond b val 0 : ℕ) : ℝ) = (val : ℝ) * (@ite ℝ P (Classical.propDecidable _) 1 0) := by
    intro P b val hiff
    cases b
    · have hnP : ¬ P := fun h => Bool.noConfusion (hiff.mp h)
      simp [hnP]
    · have hP : P := hiff.mpr rfl
      simp [hP]
  -- Ind terms (vAll 4 = pDigit pCode 4)
  have hv4 : vAll 4 = pDigit pCode 4 := rfl
  have hv3 : vAll 3 = pDigit pCode 3 := rfl
  have hind_k : ∀ (k : ℕ) (hk : k ≤ 4) (T : NTree),
      ((cond (srcStarBool mask (pDigit pCode 4) vAll k)
        (T.get (rowL + 27 * maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) =
      linIndU k hk T K := by
    intro k hk T
    unfold linIndU
    rw [hcastSucc_eq, ← hv4]
    exact hite_cond _ _ _ (srcStarPred_relabel_iff σ vAll hvAll hk)
  -- CSS 27-entry cells
  have hc27 := of_allBelow hcss27 hlc0_lt
  simp only [Bool.and_eq_true, Nat.beq_eq, natAdd_eq] at hc27
  rcases hc27 with ⟨⟨⟨⟨⟨⟨⟨⟨hchi1, hchi2⟩, hchi3⟩, hss1⟩, hss2⟩, hss3⟩, hu1⟩, _⟩, _⟩
  have hcss1_real := evalCssListU_eq_sums C.isTier2 1 (by decide) C.css1 K
  have hcss2_real := evalCssListU_eq_sums C.isTier2 2 (by decide) C.css2 K
  have hcss3_real := evalCssListU_eq_sums C.isTier2 3 (by decide) C.css3 K
  dsimp only at hcss1_real hcss2_real hcss3_real
  rw [hembInit2_eq, ← hchi1, ← hss1] at hcss1_real
  rw [hembInit2_eq, ← hchi2, ← hss2] at hcss2_real
  rw [hembInit2_eq, ← hchi3, ← hss3] at hcss3_real
  have hchi_cond : ∀ (k : ℕ) (hk : k ≤ 3) (T : NTree),
      ((cond (chiPairBool mask (pDigit pCode 3) (pDigit pCode 4) vAll k)
        (T.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) =
      (T.get (maskSubTritCode mask vL0 3) : ℝ) *
        (@ite ℝ (chiPred2 k hk K) (Classical.propDecidable _) 1 0) := by
    intro k hk T
    rw [← hv3, ← hv4]
    exact hite_cond _ _ _ (chiPred2_relabel_iff σ vAll hvAll hk)
  have hss2_cond : ∀ (k : ℕ) (hk : k ≤ 3) (T : NTree),
      ((cond (srcStarBool mask (pDigit pCode 3) vAll k)
        (T.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) =
      (T.get (maskSubTritCode mask vL0 3) : ℝ) *
        (@ite ℝ (srcStarPred2 k hk K) (Classical.propDecidable _) 1 0) := by
    intro k hk T
    rw [← hv3]
    exact hite_cond _ _ _ (srcStarPred2_relabel_iff σ vAll hvAll hk)
  have hu1_cast : (C.cssU1Tree.get (maskSubTritCode mask vL0 3) : ℝ) =
      (sumCssU1 C.isTier2 C.css1 (maskSubTritCode mask vL0 3) : ℝ) +
      (sumCssU1 C.isTier2 C.css2 (maskSubTritCode mask vL0 3) : ℝ) +
      (sumCssU1 C.isTier2 C.css3 (maskSubTritCode mask vL0 3) : ℝ) := by
    have hc : ((C.cssU1Tree.get (maskSubTritCode mask vL0 3) : ℕ) : ℝ) =
        ((sumCssU1 C.isTier2 C.css1 (maskSubTritCode mask vL0 3) +
          sumCssU1 C.isTier2 C.css2 (maskSubTritCode mask vL0 3) +
          sumCssU1 C.isTier2 C.css3 (maskSubTritCode mask vL0 3) : ℕ) : ℝ) := by
      exact_mod_cast hu1
    push_cast at hc; linarith
  unfold IntervalM5Cert.evalPermU IntervalM5Cert.uBias IntervalM5Cert.U_fn
  simp only [natAdd_eq, natMul_eq]
  push_cast
  change ((cond (adjBool mask (pDigit pCode 0) (pDigit pCode 1))
        (C.lamTree.get (maskSubTritCode mask vSkip 4)) C.lamOff : ℕ) : ℝ) +
      (C.q0Tree.get (maskSubTritCode mask vL0 3 * 27 + maskSubTritCode mask vR0 3) : ℝ) +
      (C.q3Tree.get (maskSubTritCode mask vL0 3 * 729 + rowL * 27 + rowR) : ℝ) +
      (((cond (srcStarBool mask (pDigit pCode 4) vAll 1)
          (C.ind1Tree.get (rowL + 27 * maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
        ((cond (srcStarBool mask (pDigit pCode 4) vAll 2)
          (C.ind2Tree.get (rowL + 27 * maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
        (((cond (srcStarBool mask (pDigit pCode 4) vAll 3)
          (C.ind3Tree.get (rowL + 27 * maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
        ((cond (srcStarBool mask (pDigit pCode 4) vAll 4)
          (C.ind4Tree.get (rowL + 27 * maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ)) +
      ((((cond (chiPairBool mask (pDigit pCode 3) (pDigit pCode 4) vAll 1)
            (C.chi1Tree.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
          ((cond (chiPairBool mask (pDigit pCode 3) (pDigit pCode 4) vAll 2)
            (C.chi2Tree.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
          (((cond (chiPairBool mask (pDigit pCode 3) (pDigit pCode 4) vAll 3)
            (C.chi3Tree.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
          ((cond (srcStarBool mask (pDigit pCode 3) vAll 1)
            (C.ss1Tree.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ))) +
        (((cond (srcStarBool mask (pDigit pCode 3) vAll 2)
            (C.ss2Tree.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
          ((cond (srcStarBool mask (pDigit pCode 3) vAll 3)
            (C.ss3Tree.get (maskSubTritCode mask vL0 3)) 0 : ℕ) : ℝ) +
          (C.cssU1Tree.get (maskSubTritCode mask vL0 3) : ℝ)))) = _
  rw [huDeg_real, hq0_real, hq3_real,
    hind_k 1 (by decide) C.ind1Tree,
    hind_k 2 (by decide) C.ind2Tree,
    hind_k 3 (by decide) C.ind3Tree,
    hind_k 4 (by decide) C.ind4Tree,
    hchi_cond 1 (by decide) C.chi1Tree,
    hchi_cond 2 (by decide) C.chi2Tree,
    hchi_cond 3 (by decide) C.chi3Tree,
    hss2_cond 1 (by decide) C.ss1Tree,
    hss2_cond 2 (by decide) C.ss2Tree,
    hss2_cond 3 (by decide) C.ss3Tree,
    hu1_cast, hcss1_real, hcss2_real, hcss3_real]
  ring

private lemma evalPermV_eq (C : IntervalM5Cert) (htab : C.checkTables = true)
    (mask : ℕ) (p : Fin 120) :
    (C.evalPermV mask (C.perms5Tree.get p.1) : ℝ) =
      (C.vBias : ℝ) +
        C.V_fn ((maskGraph 5 mask).relabel
          (permOfValid (validPerm_of_checkPerms5 (C.checkPerms5_of_checkTables htab) p))) := by
  let pCode := C.perms5Tree.get p.1
  let hpv := validPerm_of_checkPerms5 (C.checkPerms5_of_checkTables htab) p
  let σ := permOfValid hpv
  let K := (maskGraph 5 mask).relabel σ
  have htab' := htab
  unfold IntervalM5Cert.checkTables at htab'
  simp only [Bool.and_eq_true, natLtBool_eq_true_iff, Nat.ble_eq] at htab'
  rcases htab' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlam_bdd, _⟩, _⟩, hind1⟩, hind2⟩, hind3⟩, hind4⟩, _⟩, _⟩, _⟩, hcss27⟩
  rcases hlam_bdd with ⟨_, hlam_bdd⟩
  let vAll : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 1)
        (cond (Nat.beq i 2) (pDigit pCode 2)
          (cond (Nat.beq i 3) (pDigit pCode 3) (pDigit pCode 4))))
  have hvAll : ∀ j : Fin 5, vAll j.1 = (σ j).1 := fun j => by
    fin_cases j <;> simp only [σ, permOfValid_val] <;> rfl
  let vSkip : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 2)
        (cond (Nat.beq i 2) (pDigit pCode 3) (pDigit pCode 4)))
  have hc4_skip_eq : graphTritCode (K.pullback embSkipOne) = maskSubTritCode mask vSkip 4 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embSkipOne) vSkip fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  have hc4_skip_lt : maskSubTritCode mask vSkip 4 < 729 := by
    rw [← hc4_skip_eq]; exact graphTritCode_lt _
  have hlv_le : C.lamTree.get (maskSubTritCode mask vSkip 4) ≤ 2 * C.lamOff :=
    natBle_eq_true_iff.mp (of_allBelow hlam_bdd hc4_skip_lt)
  let vL0 : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0) (cond (Nat.beq i 1) (pDigit pCode 1) (pDigit pCode 2))
  let vL3 : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 1)
        (cond (Nat.beq i 2) (pDigit pCode 2) (pDigit pCode 3)))
  have hlc0_eq : graphTritCode (K.pullback (embInit2 (r := 3))) =
      maskSubTritCode mask vL0 3 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embInit2 (r := 3)) vL0 fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  have hlc0_lt : maskSubTritCode mask vL0 3 < 27 := by rw [← hlc0_eq]; exact graphTritCode_lt _
  have hcastSucc_eq : graphTritCode (K.pullback Fin.castSucc) =
      packRowTrits mask (pDigit pCode 3) vL0 0 3 + 27 * maskSubTritCode mask vL0 3 :=
    graphTritCode_pullback_maskGraph mask (σ ∘ Fin.castSucc) vL3
      (fun i => by fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl)
  let rowL := packRowTrits mask (pDigit pCode 3) vL0 0 3
  let c4_init := rowL + 27 * maskSubTritCode mask vL0 3
  have hc4_init_lt : c4_init < 729 := by
    dsimp only [c4_init, rowL]
    rw [← hcastSucc_eq]; exact graphTritCode_lt _
  have hv4 : vAll 4 = pDigit pCode 4 := rfl
  have hindV_k : ∀ (k : ℕ) (hk : k ≤ 4) (mb : ℕ) (T : NTree),
      checkIndTree k 4 mb T = true →
      ((cond (allInBool mask (pDigit pCode 4) vAll k) mb (Nat.sub mb (T.get c4_init)) : ℕ) : ℝ) =
        (mb : ℝ) + linIndV k hk T K := by
    intro k hk mb T hchk
    have hcell := of_allBelow hchk hc4_init_lt
    simp only [Bool.and_eq_true, Nat.ble_eq] at hcell
    unfold linIndV
    rw [hcastSucc_eq]
    have hiff := allInPred_relabel_iff (mask := mask) σ vAll hvAll hk
    rw [hv4] at hiff
    cases hb : allInBool mask (pDigit pCode 4) vAll k
    · have hnP : ¬ allInPred k hk K := fun h => Bool.noConfusion (hb ▸ hiff.mp h)
      simp only [Bool.cond_false, natSub_eq, hnP, ↓reduceIte]
      rw [Nat.cast_sub hcell.1]; ring
    · have hP : allInPred k hk K := hiff.mpr hb
      simp [hP]
  have hc27 := of_allBelow hcss27 hlc0_lt
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, natAdd_eq] at hc27
  rcases hc27 with ⟨⟨_, hv1_eq⟩, hv1_le⟩
  have hvCss_real : ((Nat.sub C.cssV1Max (C.cssV1Tree.get (maskSubTritCode mask vL0 3)) : ℕ) : ℝ) =
      (C.cssV1Max : ℝ) +
        evalCssListV C.isTier2 1 (by decide) C.css1 K +
        evalCssListV C.isTier2 2 (by decide) C.css2 K +
        evalCssListV C.isTier2 3 (by decide) C.css3 K := by
    simp only [natSub_eq]
    rw [Nat.cast_sub hv1_le,
      evalCssListV_eq_sum C.isTier2 1 (by decide) C.css1 K,
      evalCssListV_eq_sum C.isTier2 2 (by decide) C.css2 K,
      evalCssListV_eq_sum C.isTier2 3 (by decide) C.css3 K,
      hlc0_eq]
    have hc : ((C.cssV1Tree.get (maskSubTritCode mask vL0 3) : ℕ) : ℝ) =
        ((sumCssSs C.isTier2 C.css1 (maskSubTritCode mask vL0 3) +
          sumCssSs C.isTier2 C.css2 (maskSubTritCode mask vL0 3) +
          sumCssSs C.isTier2 C.css3 (maskSubTritCode mask vL0 3) : ℕ) : ℝ) := by
      exact_mod_cast hv1_eq
    push_cast at hc; linarith
  have hvDeg_real : ((Nat.sub (Nat.mul 2 C.lamOff) (C.lamTree.get (maskSubTritCode mask vSkip 4)) : ℕ) : ℝ) =
      (C.lamOff : ℝ) +
        degAffineV (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) K := by
    unfold degAffineV
    simp only [natSub_eq, natMul_eq]
    rw [Nat.cast_sub hlv_le, hc4_skip_eq]
    push_cast; ring
  unfold IntervalM5Cert.evalPermV IntervalM5Cert.vBias IntervalM5Cert.V_fn
  simp only [natAdd_eq]
  push_cast
  change ((Nat.sub (Nat.mul 2 C.lamOff) (C.lamTree.get (maskSubTritCode mask vSkip 4)) : ℕ) : ℝ) +
      (((cond (allInBool mask (pDigit pCode 4) vAll 1) C.m1_bdd
          (Nat.sub C.m1_bdd (C.ind1Tree.get c4_init)) : ℕ) : ℝ) +
        ((cond (allInBool mask (pDigit pCode 4) vAll 2) C.m2_bdd
          (Nat.sub C.m2_bdd (C.ind2Tree.get c4_init)) : ℕ) : ℝ) +
        (((cond (allInBool mask (pDigit pCode 4) vAll 3) C.m3_bdd
          (Nat.sub C.m3_bdd (C.ind3Tree.get c4_init)) : ℕ) : ℝ) +
        ((cond (allInBool mask (pDigit pCode 4) vAll 4) C.m4_bdd
          (Nat.sub C.m4_bdd (C.ind4Tree.get c4_init)) : ℕ) : ℝ))) +
      ((Nat.sub C.cssV1Max (C.cssV1Tree.get (maskSubTritCode mask vL0 3)) : ℕ) : ℝ) = _
  rw [hvDeg_real,
    hindV_k 1 (by decide) C.m1_bdd C.ind1Tree hind1,
    hindV_k 2 (by decide) C.m2_bdd C.ind2Tree hind2,
    hindV_k 3 (by decide) C.m3_bdd C.ind3Tree hind3,
    hindV_k 4 (by decide) C.m4_bdd C.ind4Tree hind4,
    hvCss_real]
  ring

/-- **Master Soundness Theorem for `IntervalM5Cert`**:
Given `cStar ≤ cn_hi / cd_hi`, if `C.checkTables = true` and `C.checkModelsSlice 0 317 = true`,
then EVERY finite nonempty simple digraph with `δ⁺(G) ≥ (cn_lo / cd_lo) * |V|` contains a
directed cycle of length `≤ 3`! -/
theorem IntervalM5Cert.hasCycleLe3 (C : IntervalM5Cert)
    (hcStar_hi : cStar ≤ (C.cn_hi : ℝ) / (C.cd_hi : ℝ))
    (htab : C.checkTables = true)
    (hmod : C.checkModelsSlice 0 317 = true) :
    ∀ {V : Type*} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj],
      (∀ u : V, ((C.cn_lo : ℝ) / (C.cd_lo : ℝ)) * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) →
      G.HasCycleLe3 := by
  intro V _ _ G _ hdeg
  have htab_orig := htab
  have hperms := C.checkPerms5_of_checkTables htab
  unfold IntervalM5Cert.checkTables at htab
  simp only [Bool.and_eq_true, natLtBool_eq_true_iff, Nat.ble_eq, natMul_eq] at htab
  rcases htab with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcd_lo, hcd_hi⟩, hle_frac⟩, _⟩, _⟩, _⟩, _⟩, hind1⟩, hind2⟩, hind3⟩, hind4⟩, hcss1⟩, hcss2⟩, hcss3⟩, _⟩
  have hcd_lo_pos : (0 : ℝ) < (C.cd_lo : ℝ) := Nat.cast_pos.mpr hcd_lo
  have hcd_hi_pos : (0 : ℝ) < (C.cd_hi : ℝ) := Nat.cast_pos.mpr hcd_hi
  have hc_le : (C.cn_lo : ℝ) / (C.cd_lo : ℝ) ≤ (C.cn_hi : ℝ) / (C.cd_hi : ℝ) := by
    rw [div_le_div_iff₀ hcd_lo_pos hcd_hi_pos]
    exact_mod_cast hle_frac
  let M_ind : ℝ := ((C.m1_bdd + C.m2_bdd + C.m3_bdd + C.m4_bdd : ℕ) : ℝ)
  let δ : ℝ := min (1 / (C.cd_lo : ℝ)) (1 / (C.cd_hi : ℝ))
  have hδ_pos : 0 < δ := lt_min (div_pos one_pos hcd_lo_pos) (div_pos one_pos hcd_hi_pos)
  let V_max : ℝ := ((120 * C.vBias : ℕ) : ℝ)
  -- Helper evaluating symPerm U_fn, symPerm V_fn, and model slice bounds for any C₃-free H on Fin 5:
  have hmodel_eval : ∀ (H : OrientedGraph (Fin 5)), H.TriangleFree →
      ∃ gi : ℕ,
        let mask := models5Tree.get gi
        let sumU := sumRange (fun p => C.evalPermU mask (C.perms5Tree.get p)) 0 120
        let sumV := sumRange (fun p => C.evalPermV mask (C.perms5Tree.get p)) 0 120
        symPerm C.U_fn H = (sumU : ℝ) - 120 * (C.uBias : ℝ) ∧
        symPerm C.V_fn H = (sumV : ℝ) - 120 * (C.vBias : ℝ) ∧
        C.cd_lo * sumU + C.cn_lo * sumV + 1 ≤ 120 * (C.cd_lo * C.uBias + C.cn_lo * C.vBias) ∧
        C.cd_hi * sumU + C.cn_hi * sumV + 1 ≤ 120 * (C.cd_hi * C.uBias + C.cn_hi * C.vBias) ∧
        sumV ≤ 240 * C.vBias := by
    intro H hH
    obtain ⟨gi, hgi_lt, π, hπ⟩ := canon_completeness_5 H hH
    refine ⟨gi, ?_⟩
    dsimp only
    let mask := models5Tree.get gi
    have hU : symPerm C.U_fn H =
        (sumRange (fun p => C.evalPermU mask (C.perms5Tree.get p)) 0 120 : ℝ) - 120 * (C.uBias : ℝ) := by
      rw [← symPerm_relabel C.U_fn H π, hπ,
        symPerm_eq_fin120_sum hperms C.U_fn (maskGraph 5 mask),
        sumRange_zero_eq_fin_sum (by norm_num)]
      have heach : ∀ p ∈ (Finset.univ : Finset (Fin 120)),
          (C.evalPermU mask (C.perms5Tree.get p.1) : ℝ) =
            (C.uBias : ℝ) + C.U_fn ((maskGraph 5 mask).relabel
              (permOfValid (validPerm_of_checkPerms5 hperms p))) :=
        fun p _ => evalPermU_eq C htab_orig mask p
      rw [Finset.sum_congr rfl heach, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hV : symPerm C.V_fn H =
        (sumRange (fun p => C.evalPermV mask (C.perms5Tree.get p)) 0 120 : ℝ) - 120 * (C.vBias : ℝ) := by
      rw [← symPerm_relabel C.V_fn H π, hπ,
        symPerm_eq_fin120_sum hperms C.V_fn (maskGraph 5 mask),
        sumRange_zero_eq_fin_sum (by norm_num)]
      have heach : ∀ p ∈ (Finset.univ : Finset (Fin 120)),
          (C.evalPermV mask (C.perms5Tree.get p.1) : ℝ) =
            (C.vBias : ℝ) + C.V_fn ((maskGraph 5 mask).relabel
              (permOfValid (validPerm_of_checkPerms5 hperms p))) :=
        fun p _ => evalPermV_eq C htab_orig mask p
      rw [Finset.sum_congr rfl heach, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hslice := of_allBelow hmod hgi_lt
    simp only [Bool.and_eq_true, natLtBool_eq_true_iff, Nat.ble_eq, natAdd_eq, natMul_eq, zero_add] at hslice
    rcases hslice with ⟨⟨hlo_lt, hhi_lt⟩, hsumV_le⟩
    exact ⟨hU, hV, hlo_lt, hhi_lt, hsumV_le⟩
  have hsym_lin : ∀ (c : ℝ) (H : OrientedGraph (Fin 5)),
      symPerm (fun K => C.U_fn K + c * C.V_fn K) H = symPerm C.U_fn H + c * symPerm C.V_fn H := by
    intro c H
    unfold symPerm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine hasCycleLe3_of_interval_certificate (M_ind := M_ind) (V_max := V_max)
    hc_le hcStar_hi (Nat.cast_nonneg _)
    C.U_fn C.V_fn ?_ hδ_pos (Nat.cast_nonneg _) ?_ ?_ ?_ G hdeg
  · intro n hn c₀ ε hε G₀ dG₀ hG₀_tri hG₀_reg hG₀_hered
    have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let _ : DecidableRel G₀.adj := dG₀
    let hw : IsProbWeight (unifWeight (Fin n)) := isProbWeight_unifWeight
    have hsplit : ∀ x : Fin 5 → Fin n,
        tupleWeight (unifWeight (Fin n)) x * (C.U_fn (G₀.pullback x) + c₀ * C.V_fn (G₀.pullback x)) =
        (tupleWeight (unifWeight (Fin n)) x *
          (degAffineU (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) (G₀.pullback x) +
            c₀ * degAffineV (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x * evalSosList (k := 1) (d := 2) C.facs1 (G₀.pullback x)) +
        (tupleWeight (unifWeight (Fin n)) x * evalSosList (k := 3) (d := 1) C.facs3 (G₀.pullback x)) +
        (tupleWeight (unifWeight (Fin n)) x *
          (linIndU 1 (by decide) C.ind1Tree (G₀.pullback x) +
            c₀ * linIndV 1 (by decide) C.ind1Tree (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x *
          (linIndU 2 (by decide) C.ind2Tree (G₀.pullback x) +
            c₀ * linIndV 2 (by decide) C.ind2Tree (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x *
          (linIndU 3 (by decide) C.ind3Tree (G₀.pullback x) +
            c₀ * linIndV 3 (by decide) C.ind3Tree (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x *
          (linIndU 4 (by decide) C.ind4Tree (G₀.pullback x) +
            c₀ * linIndV 4 (by decide) C.ind4Tree (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x *
          (evalCssListU C.isTier2 1 (by decide) C.css1 (G₀.pullback x) +
            c₀ * evalCssListV C.isTier2 1 (by decide) C.css1 (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x *
          (evalCssListU C.isTier2 2 (by decide) C.css2 (G₀.pullback x) +
            c₀ * evalCssListV C.isTier2 2 (by decide) C.css2 (G₀.pullback x))) +
        (tupleWeight (unifWeight (Fin n)) x *
          (evalCssListU C.isTier2 3 (by decide) C.css3 (G₀.pullback x) +
            c₀ * evalCssListV C.isTier2 3 (by decide) C.css3 (G₀.pullback x))) :=
      fun x => by unfold IntervalM5Cert.U_fn IntervalM5Cert.V_fn; ring
    simp_rw [hsplit]
    simp only [Finset.sum_add_distrib]
    have h0 := expect_degAffine_eq_zero (r := 3) G₀ hw hG₀_reg
      (fun K4 : OrientedGraph (Fin 4) => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ))
    have hs1 := expect_evalSosList_nonneg G₀ hw (k := 1) (d := 2) C.facs1
    have hs3 := expect_evalSosList_nonneg G₀ hw (k := 3) (d := 1) C.facs3
    have hi1 := expect_linInd_ge hn (by decide) (by norm_num) hind1 G₀ hG₀_tri hε.le hG₀_reg hG₀_hered
    have hi2 := expect_linInd_ge hn (by decide) (by norm_num) hind2 G₀ hG₀_tri hε.le hG₀_reg hG₀_hered
    have hi3 := expect_linInd_ge hn (by decide) (by norm_num) hind3 G₀ hG₀_tri hε.le hG₀_reg hG₀_hered
    have hi4 := expect_linInd_ge hn (by decide) (by norm_num) hind4 G₀ hG₀_tri hε.le hG₀_reg hG₀_hered
    have hc1 := expect_evalCssList_nonneg hn C.isTier2 (by decide) (by norm_num) G₀ hG₀_tri hG₀_reg hcss1
    have hc2 := expect_evalCssList_nonneg hn C.isTier2 (by decide) (by norm_num) G₀ hG₀_tri hG₀_reg hcss2
    have hc3 := expect_evalCssList_nonneg hn C.isTier2 (by decide) (by norm_num) G₀ hG₀_tri hG₀_reg hcss3
    dsimp only [M_ind]
    push_cast
    linarith
  · intro H hH
    obtain ⟨gi, hU, hV, hlo, _, _⟩ := hmodel_eval H hH
    rw [hsym_lin, hU, hV]
    have hcast : ((C.cd_lo * sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 +
        C.cn_lo * sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 + 1 : ℕ) : ℝ) ≤
        ((120 * (C.cd_lo * C.uBias + C.cn_lo * C.vBias) : ℕ) : ℝ) := by
      exact_mod_cast hlo
    push_cast at hcast
    have hdiv : ((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
        120 * (C.uBias : ℝ)) +
        ((C.cn_lo : ℝ) / (C.cd_lo : ℝ)) *
          ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
            120 * (C.vBias : ℝ)) ≤ -(1 / (C.cd_lo : ℝ)) := by
      have hlin : ((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
          120 * (C.uBias : ℝ)) * (C.cd_lo : ℝ) +
          (C.cn_lo : ℝ) *
            ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
              120 * (C.vBias : ℝ)) ≤ -1 := by linarith
      have hmul_eq : (((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
          120 * (C.uBias : ℝ)) +
          ((C.cn_lo : ℝ) / (C.cd_lo : ℝ)) *
            ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
              120 * (C.vBias : ℝ))) * (C.cd_lo : ℝ) =
          ((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
            120 * (C.uBias : ℝ)) * (C.cd_lo : ℝ) +
            (C.cn_lo : ℝ) *
              ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
                120 * (C.vBias : ℝ)) := by
        have hcd0 : (C.cd_lo : ℝ) ≠ 0 := hcd_lo_pos.ne'
        rw [add_mul, mul_comm ((C.cn_lo : ℝ) / _), mul_assoc, div_mul_cancel₀ _ hcd0]; ring
      have hneg_eq : (-(1 / (C.cd_lo : ℝ))) * (C.cd_lo : ℝ) = -1 := by
        have hcd0 : (C.cd_lo : ℝ) ≠ 0 := hcd_lo_pos.ne'
        rw [neg_mul, one_div_mul_cancel hcd0]
      exact le_of_mul_le_mul_right (by linarith) hcd_lo_pos
    have hδ_le : δ ≤ 1 / (C.cd_lo : ℝ) := min_le_left _ _
    linarith
  · intro H hH
    obtain ⟨gi, hU, hV, _, hhi, _⟩ := hmodel_eval H hH
    rw [hsym_lin, hU, hV]
    have hcast : ((C.cd_hi * sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 +
        C.cn_hi * sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 + 1 : ℕ) : ℝ) ≤
        ((120 * (C.cd_hi * C.uBias + C.cn_hi * C.vBias) : ℕ) : ℝ) := by
      exact_mod_cast hhi
    push_cast at hcast
    have hdiv : ((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
        120 * (C.uBias : ℝ)) +
        ((C.cn_hi : ℝ) / (C.cd_hi : ℝ)) *
          ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
            120 * (C.vBias : ℝ)) ≤ -(1 / (C.cd_hi : ℝ)) := by
      have hlin : ((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
          120 * (C.uBias : ℝ)) * (C.cd_hi : ℝ) +
          (C.cn_hi : ℝ) *
            ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
              120 * (C.vBias : ℝ)) ≤ -1 := by linarith
      have hmul_eq : (((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
          120 * (C.uBias : ℝ)) +
          ((C.cn_hi : ℝ) / (C.cd_hi : ℝ)) *
            ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
              120 * (C.vBias : ℝ))) * (C.cd_hi : ℝ) =
          ((sumRange (fun p => C.evalPermU (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
            120 * (C.uBias : ℝ)) * (C.cd_hi : ℝ) +
            (C.cn_hi : ℝ) *
              ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) -
                120 * (C.vBias : ℝ)) := by
        have hcd0 : (C.cd_hi : ℝ) ≠ 0 := hcd_hi_pos.ne'
        rw [add_mul, mul_comm ((C.cn_hi : ℝ) / _), mul_assoc, div_mul_cancel₀ _ hcd0]; ring
      have hneg_eq : (-(1 / (C.cd_hi : ℝ))) * (C.cd_hi : ℝ) = -1 := by
        have hcd0 : (C.cd_hi : ℝ) ≠ 0 := hcd_hi_pos.ne'
        rw [neg_mul, one_div_mul_cancel hcd0]
      exact le_of_mul_le_mul_right (by linarith) hcd_hi_pos
    have hδ_le : δ ≤ 1 / (C.cd_hi : ℝ) := min_le_right _ _
    linarith
  · intro H hH
    obtain ⟨gi, _, hV, _, _, hv_le⟩ := hmodel_eval H hH
    rw [hV]
    have hv_nn : (0 : ℝ) ≤ (sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) :=
      Nat.cast_nonneg _
    have hv_ub : (sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) ≤
        240 * (C.vBias : ℝ) := by
      have hc : ((sumRange (fun p => C.evalPermV (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℕ) : ℝ) ≤
          ((240 * C.vBias : ℕ) : ℝ) := by exact_mod_cast hv_le
      push_cast at hc; exact hc
    dsimp only [V_max]
    push_cast
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end CaccettaHaggkvist
