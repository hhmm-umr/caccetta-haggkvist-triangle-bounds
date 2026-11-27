module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.WeightBridge
public import CaccettaHaggkvist.FlagCert
public import CaccettaHaggkvist.ExtremalBridge
public import CaccettaHaggkvist.KernelCore
public import CaccettaHaggkvist.CanonStep2to5

/-!
# Zero-Typeclass Pure-`Nat` Kernel Evaluator & Bridge for Vanilla Exact Q-SOS Certificates (`m = 5`)

Connects `FlagCert.hasCycleLe3_of_flag_certificate` (`degLinearTerm` + `sosFactorTerm`) to
zero-typeclass `Nat.*` + `cond` GMP kernel arithmetic over the 317 canonical `C₃`-free 5-vertex
oriented graphs from `CanonStep2to5.canon_completeness_5`.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

/-! ## Section 1: Pure `Nat.rec` Divide-and-Conquer `Nat` Range Summation & `allBelow` -/

lemma natAdd_eq (a b : ℕ) : Nat.add a b = a + b := rfl
lemma natSub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
lemma natMul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
lemma boolBeq_same (b : Bool) : Bool.beq b b = true := by cases b <;> rfl
lemma boolBeq_tf : Bool.beq true false = false := rfl
lemma boolBeq_ft : Bool.beq false true = false := rfl

lemma checkRangeAux_of_forall {f : ℕ → Bool} (hf : ∀ i, f i = true) :
    ∀ d lo len, len ≤ 2 ^ d → checkRangeAux f d lo len = true
  | 0, _, 0, _ => rfl
  | 0, lo, 1, _ => hf lo
  | 0, _, _ + 2, hle => by simp at hle
  | _ + 1, _, 0, _ => rfl
  | _ + 1, lo, 1, _ => hf lo
  | d + 1, lo, len' + 2, hle => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    change (checkRangeAux f d lo ((len' + 2) / 2) &&
      checkRangeAux f d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2)) = true
    rw [checkRangeAux_of_forall hf d lo ((len' + 2) / 2) (by omega),
      checkRangeAux_of_forall hf d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2) (by omega)]
    rfl

lemma checkRangeAux_congr {f g : ℕ → Bool} :
    ∀ d lo len : ℕ, (∀ i, lo ≤ i → i < lo + len → f i = g i) →
      checkRangeAux f d lo len = checkRangeAux g d lo len
  | 0, _, 0, _ => rfl
  | 0, lo, 1, h => h lo (le_refl lo) (by omega)
  | 0, _, _ + 2, _ => rfl
  | _ + 1, _, 0, _ => rfl
  | _ + 1, lo, 1, h => h lo (le_refl lo) (by omega)
  | d + 1, lo, len' + 2, h => by
    change (checkRangeAux f d lo ((len' + 2) / 2) &&
      checkRangeAux f d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2)) =
      (checkRangeAux g d lo ((len' + 2) / 2) &&
      checkRangeAux g d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2))
    rw [checkRangeAux_congr d lo ((len' + 2) / 2) (fun i h1' h2' => h i h1' (by omega)),
      checkRangeAux_congr d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2)
        (fun i h1' h2' => h i (by omega) (by omega))]

lemma allBelow_eq_true_of_forall {n : ℕ} (hn : n ≤ 2 ^ 17) {f : ℕ → Bool}
    (hf : ∀ i < n, f i = true) : allBelow n f = true := by
  unfold allBelow checkRange
  rw [checkRangeAux_congr 17 0 n (g := fun _ => true) (fun i _ hi => hf i (by omega))]
  exact checkRangeAux_of_forall (fun _ => rfl) 17 0 n hn

/-- Pure 1-argument structural recursion (`Nat.rec` on `d`, zero typeclasses) `Nat` sum. -/
def sumRangeAux (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, len => cond (Nat.beq len 0) 0 (f lo)
  | d + 1, lo, len =>
    cond (Nat.beq len 0) 0
      (cond (Nat.beq len 1) (f lo)
        (let half := Nat.div len 2
         Nat.add (sumRangeAux f d lo half)
           (sumRangeAux f d (Nat.add lo half) (Nat.sub len half))))

def sumRange (f : ℕ → ℕ) (lo len : ℕ) : ℕ :=
  sumRangeAux f 13 lo len

lemma sumRangeAux_eq_sum_Ico (f : ℕ → ℕ) :
    ∀ d lo len : ℕ, len ≤ 2 ^ d →
      (sumRangeAux f d lo len : ℝ) = ∑ i ∈ Finset.Ico lo (lo + len), (f i : ℝ)
  | 0, _, 0, _ => by simp [sumRangeAux]
  | 0, lo, 1, _ => by simp [sumRangeAux]
  | 0, _, _ + 2, hle => by simp at hle
  | _ + 1, _, 0, _ => by simp [sumRangeAux]
  | _ + 1, lo, 1, _ => by simp [sumRangeAux]
  | d + 1, lo, len' + 2, hle => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    change ((sumRangeAux f d lo ((len' + 2) / 2) +
      sumRangeAux f d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2) : ℕ) : ℝ) = _
    push_cast
    rw [sumRangeAux_eq_sum_Ico f d lo ((len' + 2) / 2) (by omega),
      sumRangeAux_eq_sum_Ico f d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2) (by omega)]
    have hadd : lo + (len' + 2) / 2 + ((len' + 2) - (len' + 2) / 2) = lo + (len' + 2) := by omega
    rw [hadd, ← Finset.sum_union
      (Finset.Ico_disjoint_Ico_consecutive lo (lo + (len' + 2) / 2) (lo + (len' + 2))),
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]

lemma sumRange_zero_eq_fin_sum {n : ℕ} (hn : n ≤ 2 ^ 13) (f : ℕ → ℕ) :
    (sumRange f 0 n : ℝ) = ∑ i : Fin n, (f i.1 : ℝ) := by
  unfold sumRange
  rw [sumRangeAux_eq_sum_Ico f 13 0 n hn, zero_add, Nat.Ico_zero_eq_range, ← Fin.sum_univ_eq_sum_range]

/-! ## Section 2: Recursive Base-3 `graphTritCode` & Zero-Typeclass `maskSubTritCode` -/

noncomputable def edgeTritG {m : ℕ} (K : OrientedGraph (Fin (m + 1))) (i : Fin m) : Fin 3 :=
  @ite (Fin 3) (K.adj i.castSucc (Fin.last m)) (Classical.propDecidable _) ⟨1, by omega⟩
    (@ite (Fin 3) (K.adj (Fin.last m) i.castSucc) (Classical.propDecidable _) ⟨2, by omega⟩
      ⟨0, by omega⟩)

/-- Exact base-3 encoding (`< 3^(r*(r-1)/2)`) of any `OrientedGraph (Fin r)`. -/
noncomputable def graphTritCode : ∀ {r : ℕ}, OrientedGraph (Fin r) → ℕ
  | 0, _ => 0
  | m + 1, K => packTrits (edgeTritG K) + (3 ^ m) * graphTritCode (K.pullback Fin.castSucc)

private lemma choose2_succ : ∀ m : ℕ, m + m * (m - 1) / 2 = (m + 1) * m / 2
  | 0 => rfl
  | k + 1 => by
    simp only [Nat.add_sub_cancel]
    have hmul : (k + 1 + 1) * (k + 1) = (k + 1) * k + (k + 1) * 2 := by ring
    rw [hmul, Nat.add_mul_div_right _ _ (by omega : 0 < 2), add_comm]

lemma graphTritCode_lt : ∀ {r : ℕ} (K : OrientedGraph (Fin r)),
    graphTritCode K < 3 ^ (r * (r - 1) / 2)
  | 0, _ => by simp [graphTritCode]
  | m + 1, K => by
    unfold graphTritCode
    have h1 := packTrits_lt (edgeTritG K)
    have h2 := graphTritCode_lt (K.pullback Fin.castSucc)
    have h2' : 1 + graphTritCode (K.pullback Fin.castSucc) ≤ 3 ^ (m * (m - 1) / 2) := by omega
    have hpow : 3 ^ m * 3 ^ (m * (m - 1) / 2) = 3 ^ ((m + 1) * m / 2) := by
      rw [← Nat.pow_add, choose2_succ m]
    simp only [Nat.add_sub_cancel]
    calc packTrits (edgeTritG K) + 3 ^ m * graphTritCode (K.pullback Fin.castSucc)
        < 3 ^ m + 3 ^ m * graphTritCode (K.pullback Fin.castSucc) := Nat.add_lt_add_right h1 _
      _ = 3 ^ m * (1 + graphTritCode (K.pullback Fin.castSucc)) := by ring
      _ ≤ 3 ^ m * 3 ^ (m * (m - 1) / 2) := Nat.mul_le_mul_left _ h2'
      _ = 3 ^ ((m + 1) * m / 2) := hpow

def pairTritBool (mask u w : ℕ) : ℕ :=
  cond (adjBool mask u w) 1 (cond (adjBool mask w u) 2 0)

def packRowTrits (mask w : ℕ) (v : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | off, len + 1 =>
    Nat.add (pairTritBool mask (v off) w)
      (Nat.mul 3 (packRowTrits mask w v (Nat.add off 1) len))

def maskSubTritCode (mask : ℕ) (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    Nat.add (packRowTrits mask (v m) v 0 m)
      (Nat.mul (Nat.pow 3 m) (maskSubTritCode mask v m))

private lemma packTrits_eq_packRowTrits (mask w : ℕ) (v : ℕ → ℕ) :
    ∀ {len : ℕ} (off : ℕ) (f : Fin len → Fin 3),
      (∀ j : Fin len, (f j).1 = pairTritBool mask (v (off + j.1)) w) →
      packTrits f = packRowTrits mask w v off len
  | 0, _, _, _ => rfl
  | len + 1, off, f, hf => by
    change (f 0).1 + 3 * packTrits (fun i => f i.succ) =
      pairTritBool mask (v off) w + 3 * packRowTrits mask w v (off + 1) len
    have h0 := hf 0
    simp only [Fin.val_zero, Nat.add_zero] at h0
    have hsucc : packTrits (fun i => f i.succ) = packRowTrits mask w v (off + 1) len :=
      packTrits_eq_packRowTrits mask w v (off + 1) (fun i => f i.succ) fun j => by
        have hj := hf j.succ
        simp only [Fin.val_succ] at hj
        have hidx : off + (j.1 + 1) = off + 1 + j.1 := by omega
        rwa [← hidx]
    rw [h0, hsucc]

lemma graphTritCode_pullback_maskGraph {m : ℕ} (mask : ℕ) :
    ∀ {r : ℕ} (emb : Fin r → Fin m) (v : ℕ → ℕ),
      (∀ i : Fin r, v i.1 = (emb i).1) →
      graphTritCode ((maskGraph m mask).pullback emb) = maskSubTritCode mask v r
  | 0, _, _, _ => rfl
  | s + 1, emb, v, hv => by
    change packTrits (edgeTritG ((maskGraph m mask).pullback emb)) +
        3 ^ s * graphTritCode (((maskGraph m mask).pullback emb).pullback Fin.castSucc) =
      packRowTrits mask (v s) v 0 s + 3 ^ s * maskSubTritCode mask v s
    have hlast : v s = (emb (Fin.last s)).1 := hv (Fin.last s)
    have hrow : packTrits (edgeTritG ((maskGraph m mask).pullback emb)) =
        packRowTrits mask (v s) v 0 s := by
      refine packTrits_eq_packRowTrits mask (v s) v 0 _ fun j => ?_
      rw [zero_add, ← Fin.val_castSucc j, hv j.castSucc, hlast]
      unfold edgeTritG pairTritBool
      change (@ite (Fin 3) (adjBool mask (emb j.castSucc).1 (emb (Fin.last s)).1 = true)
          (Classical.propDecidable _) ⟨1, _⟩
          (@ite (Fin 3) (adjBool mask (emb (Fin.last s)).1 (emb j.castSucc).1 = true)
            (Classical.propDecidable _) ⟨2, _⟩ ⟨0, _⟩)).1 = _
      cases adjBool mask (emb j.castSucc).1 (emb (Fin.last s)).1 <;>
        cases adjBool mask (emb (Fin.last s)).1 (emb j.castSucc).1 <;>
        simp
    have hsub : ((maskGraph m mask).pullback emb).pullback Fin.castSucc =
        (maskGraph m mask).pullback (emb ∘ Fin.castSucc) := rfl
    rw [hrow, hsub, graphTritCode_pullback_maskGraph mask (emb ∘ Fin.castSucc) v
      (fun i => hv i.castSucc)]

/-! ## Section 3: Zero-Typeclass Verification of `Perm (Fin 5)` Enumeration (`120` Perms) -/

def checkPerms5 (permsTree : NTree) : Bool :=
  allBelow 120 (fun p => validPerm 5 (permsTree.get p)) &&
  allBelow 120 (fun p =>
    allBelow p (fun q =>
      !(allBelow 5 (fun i => Nat.beq (pDigit (permsTree.get p) i) (pDigit (permsTree.get q) i)))))

lemma validPerm_of_checkPerms5 {permsTree : NTree} (hp : checkPerms5 permsTree = true) (p : Fin 120) :
    validPerm 5 (permsTree.get p.1) = true := by
  unfold checkPerms5 at hp
  simp only [Bool.and_eq_true] at hp
  exact of_allBelow hp.1 p.isLt

lemma symPerm_eq_fin120_sum {permsTree : NTree} (hp : checkPerms5 permsTree = true)
    (F : OrientedGraph (Fin 5) → ℝ) (H : OrientedGraph (Fin 5)) :
    symPerm F H =
      ∑ p : Fin 120, F (H.relabel (permOfValid (validPerm_of_checkPerms5 hp p))) := by
  let π5 : Fin 120 → Equiv.Perm (Fin 5) := fun p => permOfValid (validPerm_of_checkPerms5 hp p)
  unfold checkPerms5 at hp
  simp only [Bool.and_eq_true] at hp
  have hneq : ∀ {p q : Fin 120}, q.1 < p.1 → π5 p ≠ π5 q := by
    intro p q hlt heq
    have hdist := of_allBelow (of_allBelow hp.2 p.isLt) hlt
    have hall : allBelow 5 (fun i =>
        Nat.beq (pDigit (permsTree.get p.1) i) (pDigit (permsTree.get q.1) i)) = true := by
      refine allBelow_eq_true_of_forall (by norm_num) fun i hi => ?_
      have hval : (π5 p ⟨i, hi⟩).1 = (π5 q ⟨i, hi⟩).1 := by rw [heq]
      simp only [π5, permOfValid_val] at hval
      exact Nat.beq_eq.mpr hval
    rw [hall] at hdist
    cases hdist
  have hinj : Function.Injective π5 := by
    intro p q heq
    rcases lt_trichotomy p.1 q.1 with hlt | hval | hgt
    · exact (hneq hlt heq.symm).elim
    · exact Fin.ext hval
    · exact (hneq hgt heq).elim
  have hcard : Fintype.card (Fin 120) = Fintype.card (Equiv.Perm (Fin 5)) := by decide
  let e5 : Fin 120 ≃ Equiv.Perm (Fin 5) :=
    Equiv.ofBijective π5 ((Fintype.bijective_iff_injective_and_card π5).mpr ⟨hinj, hcard⟩)
  unfold symPerm
  rw [← Equiv.sum_comp e5]
  rfl

/-! ## Section 4: Rank-1 SOS Factor Lists & Zero-Typeclass `posSum`/`negSum` Table Equivalence -/

structure SosFacSpec where
  wt : ℕ
  sigCode : ℕ
  uOff : ℕ
  uTree : NTree

noncomputable def evalSosFac {k d : ℕ} (s : SosFacSpec) (K : OrientedGraph (Fin (k + d + d))) : ℝ :=
  sosFactorTerm (s.wt : ℝ)
    (fun R => cond (Nat.beq (graphTritCode R) s.sigCode) 1 0)
    (fun L => (s.uTree.get (graphTritCode L) : ℝ) - (s.uOff : ℝ))
    K

noncomputable def evalSosList {k d : ℕ} : List SosFacSpec → OrientedGraph (Fin (k + d + d)) → ℝ
  | [], _ => 0
  | s :: rest, K => evalSosFac s K + evalSosList rest K

lemma expect_evalSosList_nonneg {W : Type*} [Fintype W] {k d : ℕ}
    (H_reg : OrientedGraph W) {w : W → ℝ} (hw : IsProbWeight w) :
    ∀ facs : List SosFacSpec,
      0 ≤ ∑ x : Fin (k + d + d) → W, tupleWeight w x * evalSosList facs (H_reg.pullback x)
  | [] => by simp [evalSosList]
  | s :: rest => by
    have hsplit : ∀ x : Fin (k + d + d) → W,
        tupleWeight w x * evalSosList (s :: rest) (H_reg.pullback x) =
        tupleWeight w x * evalSosFac s (H_reg.pullback x) +
          tupleWeight w x * evalSosList rest (H_reg.pullback x) := fun x => by
      simp only [evalSosList]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hs : 0 ≤ ∑ x : Fin (k + d + d) → W, tupleWeight w x * evalSosFac s (H_reg.pullback x) :=
      expect_sosFactorTerm_nonneg H_reg hw (Nat.cast_nonneg s.wt)
        (fun R => by cases Nat.beq (graphTritCode R) s.sigCode <;> norm_num) _
    exact add_nonneg hs (expect_evalSosList_nonneg H_reg hw rest)

/-- Zero-typeclass signed product accumulator `(posSum, negSum)` for `evalSosList` on `(rc, lc, rgc)`. -/
def sosListPosNeg : List SosFacSpec → ℕ → ℕ → ℕ → ℕ × ℕ
  | [], _, _, _ => (0, 0)
  | s :: rest, rc, lc, rgc =>
    let pn := sosListPosNeg rest rc lc rgc
    cond (Nat.beq rc s.sigCode)
      (let uL := s.uTree.get lc
       let uR := s.uTree.get rgc
       let negL := natLtBool uL s.uOff
       let negR := natLtBool uR s.uOff
       let magL := cond negL (Nat.sub s.uOff uL) (Nat.sub uL s.uOff)
       let magR := cond negR (Nat.sub s.uOff uR) (Nat.sub uR s.uOff)
       let prod := Nat.mul (Nat.mul s.wt magL) magR
       cond (Bool.beq negL negR) (Nat.add pn.1 prod, pn.2) (pn.1, Nat.add pn.2 prod))
      pn

lemma sosListPosNeg_real {k d : ℕ} (facs : List SosFacSpec) (K : OrientedGraph (Fin (k + d + d))) :
    evalSosList facs K =
      ((sosListPosNeg facs (graphTritCode (K.pullback embRoot))
        (graphTritCode (K.pullback embLeft)) (graphTritCode (K.pullback embRight))).1 : ℝ) -
      ((sosListPosNeg facs (graphTritCode (K.pullback embRoot))
        (graphTritCode (K.pullback embLeft)) (graphTritCode (K.pullback embRight))).2 : ℝ) := by
  induction facs with
  | nil => simp [evalSosList, sosListPosNeg]
  | cons s rest ih =>
    simp only [evalSosList, sosListPosNeg]
    rw [ih]
    unfold evalSosFac sosFactorTerm
    dsimp only
    cases hsig : Nat.beq (graphTritCode (K.pullback embRoot)) s.sigCode
    · simp only [Bool.cond_false]; ring
    · simp only [Bool.cond_true]
      set uL := s.uTree.get (graphTritCode (K.pullback embLeft))
      set uR := s.uTree.get (graphTritCode (K.pullback embRight))
      cases hL : natLtBool uL s.uOff <;> cases hR : natLtBool uR s.uOff
      · have hleL : s.uOff ≤ uL := Nat.le_of_not_lt (natLtBool_eq_false_iff.mp hL)
        have hleR : s.uOff ≤ uR := Nat.le_of_not_lt (natLtBool_eq_false_iff.mp hR)
        simp only [Bool.cond_false, boolBeq_same, Bool.cond_true, natAdd_eq, natSub_eq, natMul_eq]
        push_cast
        rw [Nat.cast_sub hleL, Nat.cast_sub hleR]
        ring
      · have hleL : s.uOff ≤ uL := Nat.le_of_not_lt (natLtBool_eq_false_iff.mp hL)
        have hltR : uR < s.uOff := natLtBool_eq_true_iff.mp hR
        simp only [Bool.cond_false, Bool.cond_true, boolBeq_ft, natAdd_eq, natSub_eq, natMul_eq]
        push_cast
        rw [Nat.cast_sub hleL, Nat.cast_sub hltR.le]
        ring
      · have hltL : uL < s.uOff := natLtBool_eq_true_iff.mp hL
        have hleR : s.uOff ≤ uR := Nat.le_of_not_lt (natLtBool_eq_false_iff.mp hR)
        simp only [Bool.cond_true, Bool.cond_false, boolBeq_tf, natAdd_eq, natSub_eq, natMul_eq]
        push_cast
        rw [Nat.cast_sub hltL.le, Nat.cast_sub hleR]
        ring
      · have hltL : uL < s.uOff := natLtBool_eq_true_iff.mp hL
        have hltR : uR < s.uOff := natLtBool_eq_true_iff.mp hR
        simp only [Bool.cond_true, boolBeq_same, natAdd_eq, natSub_eq, natMul_eq]
        push_cast
        rw [Nat.cast_sub hltL.le, Nat.cast_sub hltR.le]
        ring

/-! ## Section 5: Complete `m = 5` Pure-`Nat` Certificate Package & Master Soundness Theorem -/

structure VanillaM5Cert where
  c_num : ℕ
  c_den : ℕ
  lamOff : ℕ
  lamTree : NTree        -- 729 entries (lam_int[b] + lamOff)
  q0Off : ℕ
  q0Tree : NTree         -- 729 entries (k=1, d=2 pre-multiplied Q0 + q0Off)
  q3Off : ℕ
  q3Tree : NTree         -- 19,683 entries (k=3, d=1 pre-multiplied Q3 + q3Off)
  facs1 : List SosFacSpec -- k=1, d=2 (1 + 2 + 2 = 5)
  facs3 : List SosFacSpec -- k=3, d=1 (3 + 1 + 1 = 5)
  perms5Tree : NTree     -- 120 base-8 permutations of Fin 5

noncomputable def VanillaM5Cert.F (C : VanillaM5Cert) (K : OrientedGraph (Fin 5)) : ℝ :=
  degLinearTerm (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ)) C.c_num C.c_den K +
  evalSosList (k := 1) (d := 2) C.facs1 K +
  evalSosList (k := 3) (d := 1) C.facs3 K

def filterFacs (rc : ℕ) : List SosFacSpec → List SosFacSpec
  | [] => []
  | s :: rest => cond (Nat.beq rc s.sigCode) (s :: filterFacs rc rest) (filterFacs rc rest)

lemma sosListPosNeg_filterFacs (rc lc rgc : ℕ) :
    ∀ facs : List SosFacSpec, sosListPosNeg (filterFacs rc facs) rc lc rgc = sosListPosNeg facs rc lc rgc
  | [] => rfl
  | s :: rest => by
    simp only [filterFacs, sosListPosNeg]
    cases hb : Nat.beq rc s.sigCode
    · simp only [Bool.cond_false]
      exact sosListPosNeg_filterFacs rc lc rgc rest
    · simp only [Bool.cond_true, sosListPosNeg, hb, sosListPosNeg_filterFacs rc lc rgc rest]

/-- Zero-typeclass pure-`Nat` table verifier. -/
def VanillaM5Cert.checkTables (C : VanillaM5Cert) : Bool :=
  natLtBool 0 C.c_den &&
  Nat.ble C.c_num C.c_den &&
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
          (Nat.add C.q3Off pn.1))))

def VanillaM5Cert.checkQ3At (C : VanillaM5Cert) (rc : ℕ) : Bool :=
  let facs_rc := filterFacs rc C.facs3
  allBelow 27 (fun rowL =>
    allBelow 27 (fun rowR =>
      let lc := Nat.add rowL (Nat.mul 27 rc)
      let rgc := Nat.add rowR (Nat.mul 27 rc)
      let pn := sosListPosNeg facs_rc rc lc rgc
      Nat.beq (Nat.add (C.q3Tree.get (Nat.add (Nat.add (Nat.mul rc 729) (Nat.mul rowL 27)) rowR)) pn.2)
        (Nat.add C.q3Off pn.1)))

def VanillaM5Cert.checkQ3Slice (C : VanillaM5Cert) (lo len : ℕ) : Bool :=
  checkRange C.checkQ3At lo len

def VanillaM5Cert.checkTablesCore (C : VanillaM5Cert) : Bool :=
  natLtBool 0 C.c_den &&
  Nat.ble C.c_num C.c_den &&
  checkPerms5 C.perms5Tree &&
  allBelow 729 (fun c4 => Nat.ble (C.lamTree.get c4) (Nat.mul 2 C.lamOff)) &&
  allBelow 27 (fun lc =>
    allBelow 27 (fun rc =>
      let pn := sosListPosNeg C.facs1 0 lc rc
      Nat.beq (Nat.add (C.q0Tree.get (Nat.add (Nat.mul lc 27) rc)) pn.2)
        (Nat.add C.q0Off pn.1)))

lemma VanillaM5Cert.checkTables_of_parts {C : VanillaM5Cert}
    (hcore : C.checkTablesCore = true)
    (hq3 : ∀ rc < 27, C.checkQ3At rc = true) :
    C.checkTables = true := by
  unfold VanillaM5Cert.checkTables VanillaM5Cert.checkTablesCore at *
  simp only [Bool.and_eq_true] at hcore ⊢
  exact ⟨hcore, allBelow_eq_true_of_forall (by norm_num) hq3⟩

lemma VanillaM5Cert.of_checkQ3Slice {C : VanillaM5Cert} {lo len rc : ℕ}
    (h : C.checkQ3Slice lo len = true) (hlo : lo ≤ rc) (hhi : rc < lo + len) :
    C.checkQ3At rc = true :=
  of_checkRange h hlo hhi

lemma checkPerms5_of_checkTables {C : VanillaM5Cert} (htab : C.checkTables = true) :
    checkPerms5 C.perms5Tree = true := by
  unfold VanillaM5Cert.checkTables at htab
  simp only [Bool.and_eq_true] at htab
  exact htab.1.1.1.2

/-- Zero-typeclass shifted pure-`Nat` evaluation of `C.F ((maskGraph 5 mask).relabel π)`. -/
def VanillaM5Cert.evalPermNat (C : VanillaM5Cert) (mask pCode : ℕ) : ℕ :=
  let v0 := pDigit pCode 0
  let v1 := pDigit pCode 1
  let v2 := pDigit pCode 2
  let v3 := pDigit pCode 3
  let v4 := pDigit pCode 4
  let vSkip : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v2 (cond (Nat.beq i 2) v3 v4))
  let c4 := maskSubTritCode mask vSkip 4
  let lv := C.lamTree.get c4
  let linNat :=
    cond (adjBool mask v0 v1)
      (Nat.sub (Nat.add (Nat.mul (Nat.mul 2 C.c_den) C.lamOff)
        (Nat.mul (Nat.sub C.c_den C.c_num) lv))
        (Nat.mul (Nat.sub C.c_den C.c_num) C.lamOff))
      (Nat.sub (Nat.mul (Nat.add (Nat.mul 2 C.c_den) C.c_num) C.lamOff)
        (Nat.mul C.c_num lv))
  let vL0 : ℕ → ℕ := fun i => cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v1 v2)
  let vR0 : ℕ → ℕ := fun i => cond (Nat.beq i 0) v0 (cond (Nat.beq i 1) v3 v4)
  let lc0 := maskSubTritCode mask vL0 3
  let rc0 := maskSubTritCode mask vR0 3
  let q0Nat := C.q0Tree.get (Nat.add (Nat.mul lc0 27) rc0)
  let rowL := packRowTrits mask v3 vL0 0 3
  let rowR := packRowTrits mask v4 vL0 0 3
  let q3Nat := C.q3Tree.get (Nat.add (Nat.add (Nat.mul lc0 729) (Nat.mul rowL 27)) rowR)
  Nat.add (Nat.add linNat q0Nat) q3Nat

/-- Zero-typeclass strict negativity check across `[offset, offset + len)` of canonical 5-models. -/
def VanillaM5Cert.checkModelsSlice (C : VanillaM5Cert) (offset len : ℕ) : Bool :=
  let bias120 := Nat.mul 120 (Nat.add (Nat.add (Nat.mul (Nat.mul 2 C.c_den) C.lamOff) C.q0Off) C.q3Off)
  allBelow len (fun localIdx =>
    let mask := models5Tree.get (Nat.add offset localIdx)
    let tot := sumRange (fun p => C.evalPermNat mask (C.perms5Tree.get p)) 0 120
    natLtBool tot bias120)

lemma VanillaM5Cert.checkModelsSlice_of_forall {C : VanillaM5Cert}
    (hall : ∀ gi < 317,
      natLtBool (sumRange (fun p => C.evalPermNat (models5Tree.get gi) (C.perms5Tree.get p)) 0 120)
        (Nat.mul 120 (Nat.add (Nat.add (Nat.mul (Nat.mul 2 C.c_den) C.lamOff) C.q0Off) C.q3Off)) = true) :
    C.checkModelsSlice 0 317 = true := by
  unfold VanillaM5Cert.checkModelsSlice
  refine allBelow_eq_true_of_forall (by norm_num) fun gi hgi => ?_
  simpa [natAdd_eq] using hall gi hgi

lemma VanillaM5Cert.of_checkModelsSlice {C : VanillaM5Cert} {offset len gi : ℕ}
    (h : C.checkModelsSlice offset len = true) (hlo : offset ≤ gi) (hhi : gi < offset + len) :
    natLtBool (sumRange (fun p => C.evalPermNat (models5Tree.get gi) (C.perms5Tree.get p)) 0 120)
      (Nat.mul 120 (Nat.add (Nat.add (Nat.mul (Nat.mul 2 C.c_den) C.lamOff) C.q0Off) C.q3Off)) = true := by
  unfold VanillaM5Cert.checkModelsSlice at h
  have h1 := of_allBelow h (i := gi - offset) (by omega)
  have heq : Nat.add offset (gi - offset) = gi := by change offset + (gi - offset) = gi; omega
  dsimp only at h1
  rw [heq] at h1
  exact h1

lemma rowTrits_lt_27 (mask w : ℕ) (v : ℕ → ℕ) : packRowTrits mask w v 0 3 < 27 := by
  have hpt : ∀ a b, pairTritBool mask a b < 3 := fun a b => by
    unfold pairTritBool
    cases adjBool mask a b <;> cases adjBool mask b a <;> decide
  have h0 := hpt (v 0) w
  have h1 := hpt (v 1) w
  have h2 := hpt (v 2) w
  change pairTritBool mask (v 0) w + 3 * (pairTritBool mask (v 1) w + 3 * (pairTritBool mask (v 2) w + 3 * 0)) < 27
  omega

private lemma evalPermNat_eq_F (C : VanillaM5Cert) (htab : C.checkTables = true)
    (mask : ℕ) (p : Fin 120) :
    (C.evalPermNat mask (C.perms5Tree.get p.1) : ℝ) =
      ((2 * C.c_den * C.lamOff + C.q0Off + C.q3Off : ℕ) : ℝ) +
        C.F ((maskGraph 5 mask).relabel
          (permOfValid (validPerm_of_checkPerms5 (checkPerms5_of_checkTables htab) p))) := by
  let pCode := C.perms5Tree.get p.1
  let hpv := validPerm_of_checkPerms5 (checkPerms5_of_checkTables htab) p
  have htab' := htab
  unfold VanillaM5Cert.checkTables at htab'
  simp only [Bool.and_eq_true, natLtBool_eq_true_iff, Nat.ble_eq] at htab'
  rcases htab' with ⟨⟨⟨⟨⟨_, hc_le⟩, _⟩, hlam_bdd⟩, hq0_eq⟩, hq3_eq⟩
  let σ := permOfValid hpv
  let K := (maskGraph 5 mask).relabel σ
  let vSkip : ℕ → ℕ := fun i =>
    cond (Nat.beq i 0) (pDigit pCode 0)
      (cond (Nat.beq i 1) (pDigit pCode 2)
        (cond (Nat.beq i 2) (pDigit pCode 3) (pDigit pCode 4)))
  have hc4_eq : graphTritCode (K.pullback embSkipOne) = maskSubTritCode mask vSkip 4 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embSkipOne) vSkip fun i => ?_
    fin_cases i <;> simp only [Function.comp_apply, σ, permOfValid_val] <;> rfl
  have hc4_lt : maskSubTritCode mask vSkip 4 < 729 := by
    rw [← hc4_eq]; exact graphTritCode_lt (K.pullback embSkipOne)
  have hlv_le : C.lamTree.get (maskSubTritCode mask vSkip 4) ≤ 2 * C.lamOff :=
    natBle_eq_true_iff.mp (of_allBelow hlam_bdd hc4_lt)
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
  have hlc0_lt : maskSubTritCode mask vL0 3 < 27 := by
    rw [← hlc0_eq]; exact graphTritCode_lt _
  have hrc0_lt : maskSubTritCode mask vR0 3 < 27 := by
    rw [← hrc0_eq]; exact graphTritCode_lt _
  have hq0_cell := Nat.beq_eq.mp (of_allBelow (of_allBelow hq0_eq hlc0_lt) hrc0_lt)
  simp only [natAdd_eq, natMul_eq] at hq0_cell
  have hq0_real : (C.q0Tree.get (maskSubTritCode mask vL0 3 * 27 + maskSubTritCode mask vR0 3) : ℝ) =
      (C.q0Off : ℝ) + evalSosList (k := 1) (d := 2) C.facs1 K := by
    rw [sosListPosNeg_real (k := 1) (d := 2) C.facs1 K, hroot1_eq, hlc0_eq, hrc0_eq]
    have hcast : ((C.q0Tree.get (maskSubTritCode mask vL0 3 * 27 + maskSubTritCode mask vR0 3) +
        (sosListPosNeg C.facs1 0 (maskSubTritCode mask vL0 3) (maskSubTritCode mask vR0 3)).2 : ℕ) : ℝ) =
        ((C.q0Off + (sosListPosNeg C.facs1 0 (maskSubTritCode mask vL0 3) (maskSubTritCode mask vR0 3)).1 : ℕ) : ℝ) := by
      exact_mod_cast hq0_cell
    push_cast at hcast
    linarith
  have hroot3_eq : graphTritCode (K.pullback (embRoot (k := 3) (d := 1))) =
      maskSubTritCode mask vL0 3 := by
    refine graphTritCode_pullback_maskGraph mask (σ ∘ embRoot (k := 3) (d := 1)) vL0 fun i => ?_
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
    push_cast at hcast
    linarith
  unfold VanillaM5Cert.evalPermNat VanillaM5Cert.F degLinearTerm
  dsimp only
  change _ = _ + (((C.lamTree.get (graphTritCode (K.pullback embSkipOne)) : ℝ) - (C.lamOff : ℝ)) * _ +
    evalSosList (k := 1) (d := 2) C.facs1 K + evalSosList (k := 3) (d := 1) C.facs3 K)
  rw [hc4_eq]
  have hadj01 : K.adj 0 1 ↔ adjBool mask (pDigit pCode 0) (pDigit pCode 1) = true := by
    change adjBool mask (σ 0).1 (σ 1).1 = true ↔ _
    simp [σ, pCode]
  set lv := C.lamTree.get (maskSubTritCode mask vSkip 4)
  cases hb01 : adjBool mask (pDigit pCode 0) (pDigit pCode 1)
  · have hnk01 : ¬ ((maskGraph 5 mask).relabel σ).adj 0 1 := fun h => by
      rw [hadj01.mp h] at hb01; cases hb01
    dsimp only [σ, hpv] at hnk01
    have hsub2 : C.c_num * lv ≤ (2 * C.c_den + C.c_num) * C.lamOff := by
      calc C.c_num * lv ≤ C.c_num * (2 * C.lamOff) := Nat.mul_le_mul_left _ hlv_le
        _ ≤ C.c_den * (2 * C.lamOff) := Nat.mul_le_mul_right _ hc_le
        _ ≤ (2 * C.c_den + C.c_num) * C.lamOff := by
          have : C.c_den * (2 * C.lamOff) = (2 * C.c_den) * C.lamOff := by ring
          rw [this]; exact Nat.mul_le_mul_right _ (by omega)
    simp only [Bool.cond_false, hnk01, ↓reduceIte, natAdd_eq, natSub_eq, natMul_eq]
    push_cast
    rw [Nat.cast_sub hsub2, hq0_real, hq3_real]
    push_cast; ring
  · have hk01 : ((maskGraph 5 mask).relabel σ).adj 0 1 := hadj01.mpr hb01
    dsimp only [σ, hpv] at hk01
    have hsub1 : (C.c_den - C.c_num) * C.lamOff ≤ 2 * C.c_den * C.lamOff + (C.c_den - C.c_num) * lv := by
      have : (C.c_den - C.c_num) * C.lamOff ≤ 2 * C.c_den * C.lamOff := by
        refine Nat.mul_le_mul_right _ ?_; omega
      omega
    simp only [Bool.cond_true, hk01, ↓reduceIte, natAdd_eq, natSub_eq, natMul_eq]
    push_cast
    rw [Nat.cast_sub hsub1, hq0_real, hq3_real]
    push_cast
    rw [Nat.cast_sub hc_le]
    ring

/-- **Master Soundness Theorem for `VanillaM5Cert`**:
If `C.checkTables = true` and `C.checkModelsSlice 0 317 = true`, then EVERY finite nonempty simple
digraph with `δ⁺(G) ≥ (C.c_num / C.c_den) * |V|` has a directed cycle of length `≤ 3`! -/
theorem VanillaM5Cert.hasCycleLe3 (C : VanillaM5Cert)
    (htab : C.checkTables = true) (hmod : C.checkModelsSlice 0 317 = true) :
    ∀ {V : Type*} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj],
      (∀ u : V, ((C.c_num : ℝ) / (C.c_den : ℝ)) * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) →
      G.HasCycleLe3 := by
  intro V _ _ G _ hdeg
  have hc_den : 0 < C.c_den := by
    unfold VanillaM5Cert.checkTables at htab
    simp only [Bool.and_eq_true, natLtBool_eq_true_iff] at htab
    exact htab.1.1.1.1.1
  have hperms : checkPerms5 C.perms5Tree = true := checkPerms5_of_checkTables htab
  refine hasCycleLe3_of_flag_certificate hc_den C.F ?_ ?_ G hdeg
  · intro W _ _ H_reg _ _ hreg
    let hw : IsProbWeight (unifWeight W) := isProbWeight_unifWeight
    have hsplit : ∀ x : Fin 5 → W,
        tupleWeight (unifWeight W) x * C.F (H_reg.pullback x) =
        tupleWeight (unifWeight W) x *
          degLinearTerm (fun K4 => (C.lamTree.get (graphTritCode K4) : ℝ) - (C.lamOff : ℝ))
            C.c_num C.c_den (H_reg.pullback x) +
        tupleWeight (unifWeight W) x * evalSosList (k := 1) (d := 2) C.facs1 (H_reg.pullback x) +
        tupleWeight (unifWeight W) x * evalSosList (k := 3) (d := 1) C.facs3 (H_reg.pullback x) :=
      fun x => by unfold VanillaM5Cert.F; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      expect_degLinearTerm_eq_zero H_reg hw hreg]
    exact add_nonneg
      (add_nonneg le_rfl (expect_evalSosList_nonneg H_reg hw (k := 1) (d := 2) C.facs1))
      (expect_evalSosList_nonneg H_reg hw (k := 3) (d := 1) C.facs3)
  · intro H hH
    obtain ⟨gi, hgi_lt, π, hπ⟩ := canon_completeness_5 H hH
    rw [← symPerm_relabel C.F H π, hπ]
    rw [symPerm_eq_fin120_sum hperms C.F (maskGraph 5 (models5Tree.get gi))]
    have hslice := natLtBool_eq_true_iff.mp (of_allBelow hmod hgi_lt)
    change sumRange (fun p => C.evalPermNat (models5Tree.get (0 + gi)) (C.perms5Tree.get p)) 0 120 <
      120 * (2 * C.c_den * C.lamOff + C.q0Off + C.q3Off) at hslice
    rw [zero_add] at hslice
    have hreal_lt : (sumRange (fun p => C.evalPermNat (models5Tree.get gi) (C.perms5Tree.get p)) 0 120 : ℝ) <
        ((120 * (2 * C.c_den * C.lamOff + C.q0Off + C.q3Off) : ℕ) : ℝ) := by
      exact_mod_cast hslice
    rw [sumRange_zero_eq_fin_sum (by norm_num)] at hreal_lt
    have heach : ∀ p ∈ (Finset.univ : Finset (Fin 120)),
        (C.evalPermNat (models5Tree.get gi) (C.perms5Tree.get p.1) : ℝ) =
          ((2 * C.c_den * C.lamOff + C.q0Off + C.q3Off : ℕ) : ℝ) +
            C.F ((maskGraph 5 (models5Tree.get gi)).relabel
              (permOfValid (validPerm_of_checkPerms5 hperms p))) :=
      fun p _ => evalPermNat_eq_F C htab (models5Tree.get gi) p
    rw [Finset.sum_congr rfl heach, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hreal_lt
    push_cast at hreal_lt
    linarith

end CaccettaHaggkvist
