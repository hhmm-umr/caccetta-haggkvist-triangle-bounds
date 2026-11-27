module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.WeightBridge

/-!
# Zero-Typeclass Pure-Kernel (`Nat.*` + `cond`) Engine & Inductive Canonical Completeness

Every function evaluated during kernel verification uses direct primitives (`Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.beq`, `Nat.ble`, `cond`) with zero typeclass
projections, giving native C++ GMP speed under pure `Eq.refl true` (`0` `native_decide`, `0`
`bv_decide`, `[propext, Classical.choice, Quot.sound]` only).
-/

@[expose] public section

namespace CaccettaHaggkvist

@[ext]
lemma OrientedGraph.ext {V : Type*} {G₁ G₂ : OrientedGraph V}
    (h : ∀ u v : V, G₁.adj u v ↔ G₂.adj u v) : G₁ = G₂ := by
  rcases G₁ with ⟨⟨adj₁, _⟩, _⟩
  rcases G₂ with ⟨⟨adj₂, _⟩, _⟩
  have hadj : adj₁ = adj₂ := funext fun u => funext fun v => propext (h u v)
  subst hadj
  rfl

/-! ## Section 1: Zero-Typeclass `NTree` & Structural `Nat.rec` Range Checker -/

inductive NTree : Type
  | empty : NTree
  | leaf : ℕ → NTree
  | node : ℕ → NTree → NTree → NTree

def NTree.get : NTree → ℕ → ℕ
  | .empty, _ => 0
  | .leaf v, idx => cond (Nat.beq idx 0) v 0
  | .node v l r, idx =>
    cond (Nat.beq idx 0) v
      (let idx' := Nat.sub idx 1
       cond (Nat.beq (Nat.mod idx' 2) 0) (l.get (Nat.div idx' 2)) (r.get (Nat.div idx' 2)))

lemma natBle_eq_true_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b :=
  Eq.to_iff Nat.ble_eq

def natLtBool (a b : ℕ) : Bool :=
  Nat.ble (Nat.succ a) b

lemma natLtBool_eq_true_iff {a b : ℕ} : natLtBool a b = true ↔ a < b :=
  Eq.to_iff Nat.ble_eq

lemma natLtBool_eq_false_iff {a b : ℕ} : natLtBool a b = false ↔ ¬ (a < b) := by
  rw [← Bool.not_eq_true, natLtBool_eq_true_iff]

/-- Pure 1-argument `Nat.rec` divide-and-conquer boolean range checker (zero typeclasses). -/
def checkRangeAux (f : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, lo, len =>
    cond (Nat.beq len 0) true (cond (Nat.beq len 1) (f lo) false)
  | d + 1, lo, len =>
    cond (Nat.beq len 0) true
      (cond (Nat.beq len 1) (f lo)
        (let half := Nat.div len 2
         (checkRangeAux f d lo half) &&
           (checkRangeAux f d (Nat.add lo half) (Nat.sub len half))))

def checkRange (f : ℕ → Bool) (lo len : ℕ) : Bool :=
  checkRangeAux f 17 lo len

lemma of_checkRangeAux {f : ℕ → Bool} : ∀ {d lo len i : ℕ},
    checkRangeAux f d lo len = true → lo ≤ i → i < lo + len → f i = true
  | 0, lo, 0, _, _, hlo, hhi => by omega
  | 0, lo, 1, i, h, hlo, hhi => by
    have hi : i = lo := by omega
    subst hi; exact h
  | 0, _, _ + 2, _, h, _, _ => Bool.noConfusion h
  | _ + 1, lo, 0, _, _, hlo, hhi => by omega
  | _ + 1, lo, 1, i, h, hlo, hhi => by
    have hi : i = lo := by omega
    subst hi; exact h
  | d + 1, lo, len' + 2, i, h, hlo, hhi => by
    change (checkRangeAux f d lo ((len' + 2) / 2) &&
        checkRangeAux f d (lo + (len' + 2) / 2) ((len' + 2) - (len' + 2) / 2)) = true at h
    simp only [Bool.and_eq_true] at h
    by_cases hlt : i < lo + (len' + 2) / 2
    · exact of_checkRangeAux h.1 hlo hlt
    · exact of_checkRangeAux h.2 (by omega) (by omega)

lemma of_checkRange {f : ℕ → Bool} {lo len i : ℕ}
    (h : checkRange f lo len = true) (hlo : lo ≤ i) (hhi : i < lo + len) : f i = true :=
  of_checkRangeAux (d := 17) h hlo hhi

def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  checkRange f 0 n

lemma of_allBelow {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) {i : ℕ} (hi : i < n) :
    f i = true :=
  of_checkRange h (Nat.zero_le i) (by omega)

/-! ## Section 2: Zero-Typeclass `8×8` Bitmask `OrientedGraph (Fin k)` & Base-3 Extensions -/

def rawBit (mask a b : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight mask (Nat.add (Nat.shiftLeft a 3) b)) 1) 1

def adjBool (mask a b : ℕ) : Bool :=
  (!(Nat.beq a b) && rawBit mask a b) && !(rawBit mask b a)

/-- Construct a guaranteed loopless, asymmetric `OrientedGraph (Fin k)` from any bitmask `mask : ℕ`. -/
def maskGraph (k mask : ℕ) : OrientedGraph (Fin k) where
  adj i j := adjBool mask i.1 j.1 = true
  loopless i h := by simp [adjBool] at h
  asymm i j hij hji := by
    simp only [adjBool, Bool.and_eq_true, Bool.not_eq_true'] at hij hji
    rw [hij.1.2] at hji
    cases hji.2

instance instDecidableRelMaskGraph (k mask : ℕ) : DecidableRel (maskGraph k mask).adj :=
  fun i j => inferInstanceAs (Decidable (adjBool mask i.1 j.1 = true))

def packTrits : ∀ {m : ℕ}, (Fin m → Fin 3) → ℕ
  | 0, _ => 0
  | _ + 1, f => (f 0).1 + 3 * packTrits (fun i => f i.succ)

lemma packTrits_lt : ∀ {m : ℕ} (f : Fin m → Fin 3), packTrits f < 3 ^ m
  | 0, _ => by simp [packTrits]
  | _ + 1, f => by
    have h0 : (f 0).1 < 3 := (f 0).isLt
    have ih := packTrits_lt (fun i => f i.succ)
    simp only [packTrits, Nat.pow_succ]
    omega

def tritAt (ext i : ℕ) : ℕ :=
  Nat.mod (Nat.div ext (Nat.pow 3 i)) 3

lemma tritAt_eq (ext i : ℕ) : tritAt ext i = (ext / (3 ^ i)) % 3 := rfl

lemma tritAt_packTrits : ∀ {m : ℕ} (f : Fin m → Fin 3) (i : Fin m),
    tritAt (packTrits f) i.1 = (f i).1
  | 0, _, i => i.elim0
  | _ + 1, f, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [tritAt_eq, packTrits, Fin.val_zero, Nat.pow_zero, Nat.div_one]
      have h0 : (f 0).1 < 3 := (f 0).isLt
      omega
    · intro j
      simp only [tritAt_eq, packTrits, Fin.val_succ, Nat.pow_succ']
      have h0 : (f 0).1 < 3 := (f 0).isLt
      rw [← Nat.div_div_eq_div_mul]
      have hdiv : ((f 0).1 + 3 * packTrits (fun k => f k.succ)) / 3 =
          packTrits (fun k => f k.succ) := by omega
      rw [hdiv]
      exact tritAt_packTrits (fun k => f k.succ) j

def extAdjBool (m baseMask ext a b : ℕ) : Bool :=
  cond (natLtBool a m)
    (cond (natLtBool b m) (adjBool baseMask a b)
      (cond (Nat.beq b m) (Nat.beq (tritAt ext a) 1) false))
    (cond (Nat.beq a m)
      (cond (natLtBool b m) (Nat.beq (tritAt ext b) 2) false)
      false)

/-! ## Section 3: Zero-Typeclass Permutations & Sharded Inductive Step Verifier -/

def pDigit (pCode i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight pCode (Nat.mul 3 i)) 7

def validPerm (k pCode : ℕ) : Bool :=
  allBelow k (fun i =>
    (natLtBool (pDigit pCode i) k) &&
      (allBelow k (fun j => (Nat.beq i j) || !(Nat.beq (pDigit pCode i) (pDigit pCode j)))))

lemma pDigit_lt_of_validPerm {k pCode : ℕ} (hv : validPerm k pCode = true) (i : Fin k) :
    pDigit pCode i.1 < k := by
  have hi := of_allBelow hv i.isLt
  simp only [Bool.and_eq_true, natLtBool_eq_true_iff] at hi
  exact hi.1

noncomputable def permOfValid {k pCode : ℕ} (hv : validPerm k pCode = true) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective (fun i : Fin k => ⟨pDigit pCode i.1, pDigit_lt_of_validPerm hv i⟩)
    (Finite.injective_iff_bijective.mp fun i j hij => by
      have hi := of_allBelow hv i.isLt
      simp only [Bool.and_eq_true] at hi
      have hj := of_allBelow hi.2 j.isLt
      have hval : pDigit pCode i.1 = pDigit pCode j.1 := congrArg Fin.val hij
      have hbeq : Nat.beq (pDigit pCode i.1) (pDigit pCode j.1) = true := Nat.beq_eq.mpr hval
      simp only [hbeq, Bool.not_true, Bool.or_false, Nat.beq_eq] at hj
      exact Fin.ext hj)

@[simp]
lemma permOfValid_val {k pCode : ℕ} (hv : validPerm k pCode = true) (i : Fin k) :
    (permOfValid hv i).1 = pDigit pCode i.1 := by
  simp [permOfValid]

def allPairsMatch (m baseMask ext pCode targetMask : ℕ) : Bool :=
  allBelow (Nat.succ m) (fun a =>
    allBelow (Nat.succ m) (fun b =>
      Bool.beq (extAdjBool m baseMask ext (pDigit pCode a) (pDigit pCode b))
        (adjBool targetMask a b)))

def checkWitnessVal (m nNext : ℕ) (prevTree nextTree : NTree) (idx w : ℕ) : Bool :=
  let p3 := Nat.pow 3 m
  let gi := Nat.div idx p3
  let ext := Nat.mod idx p3
  let baseMask := prevTree.get gi
  cond (Nat.beq (Nat.land w 1) 0)
    (let u := Nat.land (Nat.shiftRight w 1) 7
     let v := Nat.land (Nat.shiftRight w 4) 7
     ((((natLtBool u m) && (natLtBool v m)) &&
       (extAdjBool m baseMask ext u v)) &&
       (extAdjBool m baseMask ext v m)) &&
       (extAdjBool m baseMask ext m u))
    (let cidx := Nat.land (Nat.shiftRight w 1) 8191
     let pCode := Nat.shiftRight w 14
     ((natLtBool cidx nNext) &&
       (validPerm (Nat.succ m) pCode)) &&
       (allPairsMatch m baseMask ext pCode (nextTree.get cidx)))

def checkSlice (m nNext offset len : ℕ) (prevTree nextTree subWitTree : NTree) : Bool :=
  allBelow len (fun localIdx =>
    checkWitnessVal m nNext prevTree nextTree (Nat.add offset localIdx) (subWitTree.get localIdx))

lemma exists_witness_of_checkSlice {m nNext offset len : ℕ} {prevTree nextTree subWitTree : NTree}
    (h : checkSlice m nNext offset len prevTree nextTree subWitTree = true)
    {idx : ℕ} (hlo : offset ≤ idx) (hhi : idx < offset + len) :
    ∃ w : ℕ, checkWitnessVal m nNext prevTree nextTree idx w = true := by
  refine ⟨subWitTree.get (idx - offset), ?_⟩
  have h1 := of_allBelow h (i := idx - offset) (by omega)
  change checkWitnessVal m nNext prevTree nextTree (offset + (idx - offset))
    (subWitTree.get (idx - offset)) = true at h1
  have heq : offset + (idx - offset) = idx := by omega
  rwa [heq] at h1

def liftPermLast {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) where
  toFun := Fin.lastCases (Fin.last m) (fun i => (τ i).castSucc)
  invFun := Fin.lastCases (Fin.last m) (fun i => (τ.symm i).castSucc)
  left_inv x := by refine Fin.lastCases ?_ ?_ x <;> simp
  right_inv x := by refine Fin.lastCases ?_ ?_ x <;> simp

private noncomputable def edgeTrit {m : ℕ} (G' : OrientedGraph (Fin (m + 1))) (i : Fin m) : Fin 3 :=
  @ite (Fin 3) (G'.adj i.castSucc (Fin.last m)) (Classical.propDecidable _) ⟨1, by omega⟩
    (@ite (Fin 3) (G'.adj (Fin.last m) i.castSucc) (Classical.propDecidable _) ⟨2, by omega⟩
      ⟨0, by omega⟩)

private lemma adj_iff_extAdjBool {m baseMask : ℕ} {G' : OrientedGraph (Fin (m + 1))}
    (hbase : G'.pullback Fin.castSucc = maskGraph m baseMask) (x y : Fin (m + 1)) :
    G'.adj x y ↔ extAdjBool m baseMask (packTrits (edgeTrit G')) x.1 y.1 = true := by
  have hbm : Nat.beq m m = true := Nat.beq_eq.mpr rfl
  have hnm : natLtBool m m = false := natLtBool_eq_false_iff.mpr (lt_irrefl m)
  refine Fin.lastCases ?_ ?_ x
  · refine Fin.lastCases ?_ ?_ y
    · simp only [Fin.val_last, extAdjBool, hnm, hbm, Bool.cond_false, Bool.cond_true]
      exact ⟨fun h => (G'.loopless _ h).elim, fun h => Bool.noConfusion h⟩
    · intro j
      have hj : natLtBool j.1 m = true := natLtBool_eq_true_iff.mpr j.isLt
      simp only [Fin.val_last, Fin.val_castSucc, extAdjBool, hnm, hbm, hj, Bool.cond_false,
        Bool.cond_true, Nat.beq_eq, tritAt_packTrits]
      unfold edgeTrit
      by_cases h1 : G'.adj j.castSucc (Fin.last m)
      · have h2 : ¬ G'.adj (Fin.last m) j.castSucc := G'.asymm _ _ h1
        simp [h1, h2]
      · by_cases h2 : G'.adj (Fin.last m) j.castSucc <;> simp [h1, h2]
  · intro i
    have hi : natLtBool i.1 m = true := natLtBool_eq_true_iff.mpr i.isLt
    refine Fin.lastCases ?_ ?_ y
    · simp only [Fin.val_castSucc, Fin.val_last, extAdjBool, hi, hnm, hbm, Bool.cond_true,
        Bool.cond_false, Nat.beq_eq, tritAt_packTrits]
      unfold edgeTrit
      by_cases h1 : G'.adj i.castSucc (Fin.last m)
      · simp [h1]
      · by_cases h2 : G'.adj (Fin.last m) i.castSucc <;> simp [h1, h2]
    · intro j
      have hj : natLtBool j.1 m = true := natLtBool_eq_true_iff.mpr j.isLt
      simp only [Fin.val_castSucc, extAdjBool, hi, hj, Bool.cond_true]
      have hpull : (G'.pullback Fin.castSucc).adj i j ↔ (maskGraph m baseMask).adj i j := by
        rw [hbase]
      exact hpull

theorem canon_completeness_1 (H : OrientedGraph (Fin 1)) (_hH : H.TriangleFree) :
    ∃ gi, gi < 1 ∧ ∃ π : Equiv.Perm (Fin 1), H.relabel π = maskGraph 1 ((NTree.leaf 0).get gi) := by
  refine ⟨0, Nat.one_pos, Equiv.refl (Fin 1), ?_⟩
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  exact ⟨fun h => (H.loopless i h).elim, fun h => ((maskGraph 1 _).loopless i h).elim⟩

theorem canon_completeness_step {m nPrev nNext : ℕ} {prevTree nextTree : NTree}
    (ih : ∀ H' : OrientedGraph (Fin m), H'.TriangleFree →
      ∃ gi, gi < nPrev ∧ ∃ τ : Equiv.Perm (Fin m), H'.relabel τ = maskGraph m (prevTree.get gi))
    (hcheck : ∀ idx : ℕ, idx < nPrev * 3 ^ m →
      ∃ w : ℕ, checkWitnessVal m nNext prevTree nextTree idx w = true)
    (H : OrientedGraph (Fin (m + 1))) (hH : H.TriangleFree) :
    ∃ cidx, cidx < nNext ∧ ∃ π : Equiv.Perm (Fin (m + 1)),
      H.relabel π = maskGraph (m + 1) (nextTree.get cidx) := by
  have hH'_tri : (H.pullback Fin.castSucc).TriangleFree := H.triangleFree_pullback hH Fin.castSucc
  obtain ⟨gi, hgi_lt, τ, hτ_eq⟩ := ih (H.pullback Fin.castSucc) hH'_tri
  let τ_ext := liftPermLast τ
  let G' := H.relabel τ_ext
  have hG'_tri : G'.TriangleFree := H.triangleFree_pullback hH τ_ext
  have hG'_base : G'.pullback Fin.castSucc = maskGraph m (prevTree.get gi) := by
    rw [← hτ_eq]
    ext a b
    simp [G', τ_ext, liftPermLast, OrientedGraph.relabel, OrientedGraph.pullback]
  let p3 := 3 ^ m
  have hp3_pos : 0 < p3 := Nat.pow_pos (by omega)
  let ext := packTrits (edgeTrit G')
  have hext_lt : ext < p3 := packTrits_lt (edgeTrit G')
  let idx := gi * p3 + ext
  have hidx_lt : idx < nPrev * p3 := by
    have hle : gi + 1 ≤ nPrev := hgi_lt
    calc gi * p3 + ext < gi * p3 + p3 := Nat.add_lt_add_left hext_lt (gi * p3)
      _ = (gi + 1) * p3 := by ring
      _ ≤ nPrev * p3 := Nat.mul_le_mul_right p3 hle
  have hdiv : Nat.div idx (Nat.pow 3 m) = gi := by
    change idx / p3 = gi
    dsimp [idx]
    rw [mul_comm gi p3, Nat.mul_add_div hp3_pos, Nat.div_eq_of_lt hext_lt, add_zero]
  have hmod : Nat.mod idx (Nat.pow 3 m) = ext := by
    change idx % p3 = ext
    dsimp [idx]
    rw [mul_comm gi p3, Nat.mul_add_mod, Nat.mod_eq_of_lt hext_lt]
  obtain ⟨w, hwit⟩ := hcheck idx hidx_lt
  unfold checkWitnessVal at hwit
  dsimp only at hwit
  rw [hdiv, hmod] at hwit
  cases hw_even : Nat.beq (Nat.land w 1) 0
  · rw [hw_even] at hwit
    simp only [Bool.cond_false, Bool.and_eq_true, natLtBool_eq_true_iff] at hwit
    rcases hwit with ⟨⟨hcidx_lt, hv_perm⟩, hmatch⟩
    let σ := permOfValid hv_perm
    refine ⟨Nat.land (Nat.shiftRight w 1) 8191, hcidx_lt, τ_ext * σ, ?_⟩
    have hrel_comp : H.relabel (τ_ext * σ) = G'.relabel σ := rfl
    rw [hrel_comp]
    ext a b
    have hab := of_allBelow (of_allBelow hmatch a.isLt) b.isLt
    have hab_eq : extAdjBool m (prevTree.get gi) ext (pDigit (Nat.shiftRight w 14) a.1)
        (pDigit (Nat.shiftRight w 14) b.1) =
        adjBool (nextTree.get (Nat.land (Nat.shiftRight w 1) 8191)) a.1 b.1 := by
      revert hab
      cases extAdjBool m (prevTree.get gi) ext (pDigit (Nat.shiftRight w 14) a.1)
        (pDigit (Nat.shiftRight w 14) b.1) <;>
        cases adjBool (nextTree.get (Nat.land (Nat.shiftRight w 1) 8191)) a.1 b.1 <;>
        decide
    change G'.adj (σ a) (σ b) ↔ adjBool (nextTree.get (Nat.land (Nat.shiftRight w 1) 8191)) a.1 b.1 = true
    rw [adj_iff_extAdjBool hG'_base (σ a) (σ b), permOfValid_val, permOfValid_val, hab_eq]
  · exfalso
    rw [hw_even] at hwit
    simp only [Bool.cond_true, Bool.and_eq_true, natLtBool_eq_true_iff] at hwit
    rcases hwit with ⟨⟨⟨⟨hu_lt, hv_lt⟩, huv⟩, hvm⟩, hmu⟩
    let u_fin : Fin (m + 1) := ⟨Nat.land (Nat.shiftRight w 1) 7, Nat.lt_succ_of_lt hu_lt⟩
    let v_fin : Fin (m + 1) := ⟨Nat.land (Nat.shiftRight w 4) 7, Nat.lt_succ_of_lt hv_lt⟩
    have h1 : G'.adj u_fin v_fin := (adj_iff_extAdjBool hG'_base u_fin v_fin).mpr huv
    have h2 : G'.adj v_fin (Fin.last m) := (adj_iff_extAdjBool hG'_base v_fin (Fin.last m)).mpr hvm
    have h3 : G'.adj (Fin.last m) u_fin := (adj_iff_extAdjBool hG'_base (Fin.last m) u_fin).mpr hmu
    exact hG'_tri ⟨u_fin, v_fin, Fin.last m, h1, h2, h3⟩

end CaccettaHaggkvist
