module

public import CaccettaHaggkvist.SixVertexReflection

/-! # Evaluating compiled instructions from ordered flag and edge lookups -/

@[expose] public section

namespace CaccettaHaggkvist.SixVertex

structure View where
  arc : ℕ → ℕ → Bool
  prefixCode : ℕ → ℕ
  rightCode : ℕ → ℕ → ℕ
  degreeCode : ℕ → ℕ

def every (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | i+1 => every f i && f i

theorem every_iff (f : ℕ → Bool) (n : ℕ) :
    every f n = true ↔ ∀ i : Fin n, f i.val = true := by
  induction n with
  | zero => simp [every]
  | succ n ih =>
    simp only [every, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h,z⟩ i
      exact Fin.lastCases z (fun j => h j) i
    · intro h
      exact ⟨fun i => h i.castSucc, h (Fin.last n)⟩

def fromBool (b : Bool) : ℤ := cond b 1 0

private lemma fromBool_eq {P : Prop} [Decidable P] {b : Bool} (h : b = true ↔ P) :
    fromBool b = bit P := by cases b <;> simp_all [fromBool, bit]

def Local.fast {k : ℕ} : {e : ℕ} → Local k e → ℕ → (ℕ → ℕ → Bool) → ℤ × ℤ
  | _, .one, _, _ => (1,0)
  | _, .inductionTerm a _, root, edge =>
    if codeHasSinkOrWitness a k root then
      let incoming := every (fun i => edge i k) a
      let source := every (fun i => !edge k i) a && !incoming
      (fromBool source, fromBool incoming - 1)
    else (0,0)
  | _, .css a _ p q rn rd _ _ _, root, edge =>
    if codeHasSinkOrWitness a k root then
      let incoming := every (fun i => edge i k) a
      let source := every (fun i => !edge k i) a && !incoming
      let chi := incoming && every (fun i => edge i (k+1)) a && !edge k (k+1) && !edge (k+1) k
      let slope : ℤ := 2 * q * rn * rd
      (p * (rd : ℤ)^2 * fromBool chi + slope * fromBool source + q * (rn : ℤ)^2, -slope)
    else (0,0)

theorem Local.fast_eq {k e : ℕ} (L : Local k e) (K : OrientedGraph (Fin (k+e))) [DecidableRel K.adj]
    (root : ℕ) (hr : root = tritCode k (K.pullback (Fin.castAdd e)))
    (edge : ℕ → ℕ → Bool) (he : ∀ i j : Fin (k+e), edge i.val j.val = true ↔ K.adj i j) :
    L.fast root edge = L.eval K := by
  cases L with
  | one => rfl
  | inductionTerm a hk =>
    have incoming : every (fun i => edge i k) a = true ↔ allInPred a hk K := by
      rw [every_iff]
      exact forall_congr' (fun i => he ⟨i.val,by omega⟩ (Fin.last k))
    have noOut : every (fun i => !edge k i) a = true ↔ ∀ i : Fin a,
        ¬ K.adj (Fin.last k) ⟨i.val,by omega⟩ := by
      rw [every_iff]
      apply forall_congr'
      intro i
      simpa only [Bool.not_eq_true', ← Bool.not_eq_true, Fin.val_last] using
        (not_congr (he (Fin.last k) ⟨i.val,by omega⟩))
    have src : (every (fun i => !edge k i) a && !(every (fun i => edge i k) a)) = true ↔
        srcStarPred a hk K := by
      simpa only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, srcStarPred] using
        and_congr noOut (not_congr incoming)
    simp only [fast, eval, hr]
    split
    · rw [fromBool_eq src, fromBool_eq incoming]
    · rfl
  | css a hk p q rn rd hq hrd ha =>
    let v (i : Fin a) : Fin (k+2) := ⟨i.val,by omega⟩
    let x : Fin (k+2) := ⟨k,by omega⟩
    let y : Fin (k+2) := ⟨k+1,by omega⟩
    have ins (z : Fin (k+2)) : every (fun i => edge i z.val) a = true ↔
        ∀ i, K.adj (v i) z := (every_iff _ _).trans (forall_congr' fun i => he (v i) z)
    have negEdge (i j : Fin (k+2)) : (!edge i.val j.val) = true ↔ ¬ K.adj i j := by
      simpa only [Bool.not_eq_true', ← Bool.not_eq_true] using not_congr (he i j)
    have src : (every (fun i => !edge k i) a && !(every (fun i => edge i k) a)) = true ↔
        srcStarPred2 a hk K := by
      rw [Bool.and_eq_true, every_iff]
      apply and_congr (forall_congr' fun i => negEdge x (v i))
      simpa only [Bool.not_eq_true', ← Bool.not_eq_true] using not_congr (ins x)
    have chi : (every (fun i => edge i k) a && every (fun i => edge i (k+1)) a &&
        !edge k (k+1) && !edge (k+1) k) = true ↔ chiPred2 a hk K := by
      simp only [Bool.and_eq_true, and_assoc]
      exact and_congr (ins x) (and_congr (ins y) (and_congr (negEdge x y) (negEdge y x)))
    simp only [fast, eval, hr]
    split
    · rw [fromBool_eq chi, fromBool_eq src]
    · rfl

def skip (k d i : ℕ) := cond (Nat.blt i k) i (Nat.add i d)
def skipSecond (i : ℕ) := cond (Nat.beq i 0) 0 (Nat.succ i)

def rawView (mask : ℕ) (v : ℕ → ℕ) : View where
  arc i j := adjBool mask (v i) (v j)
  prefixCode k := maskSubTritCode mask v k
  rightCode k d := maskSubTritCode mask (fun i => v (skip k d i)) (Nat.add k d)
  degreeCode r := maskSubTritCode mask (fun i => v (skipSecond i)) (Nat.succ r)

def Term.fast {m : ℕ} : Term m → View → ℤ × ℤ
  | .degree r f, X =>
    let a := f (X.degreeCode r)
    (a * fromBool (X.arc 0 1), -a)
  | @Term.linear k _ L w, X =>
    let root := X.prefixCode k
    let z := w.read root
    if z = 0 then (0,0) else scale z (L.fast root X.arc)
  | .gram k d _ L B, X =>
    let z := B.value (X.prefixCode (k+d)) (X.rightCode k d)
    if z = 0 then (0,0) else scale z (L.fast (X.prefixCode k)
      (fun i j => X.arc (skip k (2*d) i) (skip k (2*d) j)))

private theorem skip_val {k d : ℕ} (i : Fin (k+d)) :
    (embRight (k := k) (d := d) i).val = skip k d i.val := by
  by_cases h : i.val < k <;> simp [embRight,skip,h,Nat.blt_eq]

private theorem loc_val {k d e : ℕ} (i : Fin (k+e)) :
    (WeightedFlag.localizer k d e i).val = skip k (2*d) i.val := by
  cases i using Fin.addCases with
  | left j => simp [WeightedFlag.localizer, WeightedFlag.roots, skip, Nat.blt_eq, j.isLt]
  | right j =>
    have hn : ¬ k + j.val < k := by omega
    simp [WeightedFlag.localizer, skip, Nat.blt_eq, hn]
    omega

theorem Term.fast_eq {m n : ℕ} (t : Term m) (mask : ℕ) (u : Fin m → Fin n) (v : ℕ → ℕ)
    (hv : ∀ i : Fin m, (u i).val = v i.val) :
    t.fast (rawView mask v) = t.eval ((maskGraph n mask).pullback u) := by
  have code {a : ℕ} (e : Fin a → Fin m) (p : ℕ → ℕ)
      (h : ∀ i : Fin a, v (e i).val = p i.val) :
      tritCode a (((maskGraph n mask).pullback u).pullback e) = maskSubTritCode mask p a := by
    rw [tritCode_eq, OrientedGraph.pullback_comp]
    exact graphTritCode_pullback_maskGraph mask _ p (fun i => ((hv (e i)).trans (h i)).symm)
  cases t with
  | degree r f =>
    have hk := code (embSkipOne (r := r)) (fun i => v (skipSecond i)) (fun i => by
      cases i using Fin.cases <;> simp [embSkipOne,skipSecond])
    have he : adjBool mask (v 0) (v 1) = true ↔
        ((maskGraph n mask).pullback u).adj 0 1 := by
      change _ ↔ adjBool mask (u 0).val (u 1).val = true
      rw [hv 0,hv 1]
      rfl
    simp only [fast, Term.eval, rawView, hk]
    rw [fromBool_eq he]
  | @linear k e L w =>
    have hk := code (Fin.castAdd e) v (fun _ => rfl)
    have he (i j : Fin (k+e)) : (rawView mask v).arc i.val j.val = true ↔
        ((maskGraph n mask).pullback u).adj i j := by
      change _ ↔ adjBool mask (u i).val (u j).val = true
      rw [hv i, hv j]; rfl
    have hl := L.fast_eq _ _ hk.symm _ he
    simp only [fast, Term.eval, rawView, hk] at hl ⊢
    by_cases hz : w.read (maskSubTritCode mask v k) = 0
    · simp [hz,scale]
    · simp [hz,hl]
  | gram k d e L B =>
    let loc := WeightedFlag.localizer k d e
    let K := (maskGraph n mask).pullback u
    have hleft := code (WeightedFlag.left k d e) v (fun _ => rfl)
    have hright := code (WeightedFlag.right k d e) (fun i => v (skip k d i)) (fun i => by
      cases i using Fin.addCases with
      | left j => simp [WeightedFlag.right, WeightedFlag.roots,skip,Nat.blt_eq,j.isLt]
      | right j => simp [WeightedFlag.right,skip,Nat.blt_eq]; congr 1; omega)
    have hr : tritCode k ((K.pullback loc).pullback (Fin.castAdd e)) =
        maskSubTritCode mask v k := by
      change tritCode k (K.pullback (loc ∘ Fin.castAdd e)) = _
      apply code
      intro i
      simp [Function.comp_apply,loc,WeightedFlag.localizer,WeightedFlag.roots]
    have he (i j : Fin (k+e)) :
        adjBool mask (v (skip k (2*d) i.val)) (v (skip k (2*d) j.val)) = true ↔
          (K.pullback loc).adj i j := by
      change _ ↔ adjBool mask (u (loc i)).val (u (loc j)).val = true
      rw [hv, hv, loc_val,loc_val]
    have hl := L.fast_eq (K.pullback loc) _ hr.symm (fun i j => adjBool mask (v (skip k (2*d) i)) (v (skip k (2*d) j))) he
    simp only [fast, Term.eval, rawView, hleft, hright, hl]
    by_cases hz : B.value (maskSubTritCode mask v (k+d))
        (maskSubTritCode mask (fun i => v (skip k d i)) (k+d)) = 0
    · simp [hz,scale]
    · simp [hz, K, loc]

def Program.fast (P : Program) (X : View) : ℤ × ℤ :=
  P.foldr (fun t tail =>
    let z := t.fast X
    (z.1 + tail.1,z.2 + tail.2)) (0,0)

theorem Program.fast_eq (P : Program) (n mask : ℕ) (u : Fin 6 → Fin n) (v : ℕ → ℕ)
    (hv : ∀ i, (u i).val = v i.val) :
    P.fast (rawView mask v) = P.eval ((maskGraph n mask).pullback u) := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    change ((t.fast _).1 + (Program.fast ts _).1, (t.fast _).2 + (Program.fast ts _).2) = _
    rw [t.fast_eq mask u v hv, ih]
    rfl

/-- Cache a projection shared by multiple blocks before folding the instruction list. -/
def cacheAt {α β : Type} [DecidableEq α] (i : α) (f : α → β) : α → β :=
  let z := f i
  fun j => if j = i then z else f j

private theorem cacheAt_eq {α β : Type} [DecidableEq α] (i : α) (f : α → β) : cacheAt i f = f := by
  funext j
  by_cases h : j = i <;> simp [cacheAt,h]

def cached (X : View) : View :=
  let p := cacheAt 5 (cacheAt 4 (cacheAt 3 (cacheAt 2 (cacheAt 1 X.prefixCode))))
  let r := cacheAt (4,1) (cacheAt (2,2) (cacheAt (0,3) (cacheAt (3,1) (cacheAt (1,2)
    (cacheAt (2,1) (fun z : ℕ × ℕ => X.rightCode z.1 z.2))))))
  { X with prefixCode := p, rightCode := fun k d => r (k,d) }

theorem cached_eq (X : View) : cached X = X := by simp [cached,cacheAt_eq]

def fastModelRow (P : Program) (table mask : ℕ) : ℤ × ℤ :=
  sumRows (fun i =>
    let p := permutationAt table i
    let v := fun j => Nat.mod (pDigit p j) 6
    P.fast (cached (rawView mask v))) 720

theorem fastModelRow_eq (P : Program) (table mask : ℕ) :
    fastModelRow P table mask = modelRow P table mask := by
  unfold fastModelRow modelRow
  congr 1
  funext i
  dsimp only
  rw [cached_eq]
  exact P.fast_eq 6 mask (coord table i) _ (fun _ => rfl)

end CaccettaHaggkvist.SixVertex
