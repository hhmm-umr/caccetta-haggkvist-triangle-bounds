module

public import CaccettaHaggkvist.SixVertexGroups

/-! # Packing ordered flag projections for sixteen permutations at once

A projected ternary graph code is a nonnegative linear function of the host
adjacency indicators. It suffices to check the packing table on single arcs.
Both packing radices are powers of two. The graph code bound prevents carries.
-/

@[expose] public section

namespace CaccettaHaggkvist.SixVertex.Geometry

def pack (b : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, off => Nat.add (f off) (Nat.mul b (pack b f n (Nat.succ off)))

private theorem pack_congr (b : ℕ) (f g : ℕ → ℕ) (n off : ℕ)
    (h : ∀ i, off ≤ i → i < off+n → f i = g i) : pack b f n off = pack b g n off := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih => rw [pack, pack, h off (by omega) (by omega), ih _ (fun i ha hb => h i (by omega) (by omega))]

private theorem pack_sum {T : Type} [Fintype T] (b : ℕ) (w : T → ℕ) (f : T → ℕ → ℕ) (n off : ℕ) :
    (∑ t, w t * pack b (f t) n off) = pack b (fun j => ∑ t, w t * f t j) n off := by
  induction n generalizing off with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack, Nat.add_eq, Nat.mul_eq]
    rw [← ih (off+1), Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem pack_lt (b : ℕ) (_hb : 0 < b) (f : ℕ → ℕ) (n off : ℕ)
    (h : ∀ i, off ≤ i → i < off+n → f i < b) : pack b f n off < b^n := by
  induction n generalizing off with
  | zero => simp [pack]
  | succ n ih =>
    have ht := ih (off+1) (fun i ha hhi => h i (by omega) (by omega))
    have hm := Nat.mul_le_mul_left b (Nat.succ_le_of_lt ht)
    have h0 := h off le_rfl (by omega)
    change f off + b*pack b f n (off+1) < b^(n+1)
    rw [pow_succ']; nlinarith

def lane (bits x i : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight x (Nat.mul bits i)) (Nat.shiftLeft 1 bits)

private theorem lane_pack (bits : ℕ) (f : ℕ → ℕ) (n off i : ℕ) (hi : i < n)
    (h : ∀ j, off ≤ j → j < off+n → f j < 2^bits) :
    lane bits (pack (2^bits) f n off) i = f (off+i) := by
  have form (x j : ℕ) : lane bits x j = x / (2^bits)^j % (2^bits) := by
    simp [lane, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_mul]
    rfl
  rw [form]
  induction n generalizing off i with
  | zero => omega
  | succ n ih =>
    let b := 2^bits
    have hb : 0 < b := Nat.pow_pos (by decide)
    have h0 := h off le_rfl (by omega)
    change (f off + b * pack b f n (off+1)) / b^i % b = _
    cases i with
    | zero => simp [Nat.add_mul_mod_self_left, b, Nat.mod_eq_of_lt h0]
    | succ i =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt h0, zero_add]
      exact (ih (off+1) i (by omega) (fun j ha hh => h j (by omega) (by omega))).trans
        (congrArg f (by omega))

def rowWith (g : ℕ → ℕ → ℕ) (j : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | len+1, off => Nat.add (g off j) (Nat.mul 3 (rowWith g j len (Nat.succ off)))

def codeWith (g : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => Nat.add (rowWith g k k 0) (Nat.mul (Nat.pow 3 k) (codeWith g k))

private theorem row_sum {T : Type} [Fintype T] (w : T → ℕ) (g : T → ℕ → ℕ → ℕ) (j len off : ℕ) :
    (∑ t, w t * rowWith (g t) j len off) = rowWith (fun i b => ∑ t, w t * g t i b) j len off := by
  induction len generalizing off with
  | zero => simp [rowWith]
  | succ n ih =>
    simp only [rowWith, Nat.add_eq, Nat.mul_eq]
    rw [← ih (off+1), Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem code_sum {T : Type} [Fintype T] (w : T → ℕ) (g : T → ℕ → ℕ → ℕ) (n : ℕ) :
    (∑ t, w t * codeWith (g t) n) = codeWith (fun i j => ∑ t, w t * g t i j) n := by
  induction n with
  | zero => simp [codeWith]
  | succ n ih =>
    simp only [codeWith, Nat.add_eq, Nat.mul_eq]
    rw [← row_sum w g n n 0, ← ih, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem code_mask (mask : ℕ) (v : ℕ → ℕ) (n : ℕ) :
    codeWith (fun i j => pairTritBool mask (v i) (v j)) n = maskSubTritCode mask v n := by
  have row (j len off : ℕ) :
      rowWith (fun i l => pairTritBool mask (v i) (v l)) j len off =
        packRowTrits mask (v j) v off len := by
    induction len generalizing off with
    | zero => rfl
    | succ n ih => rw [rowWith, packRowTrits, ih]
  induction n with
  | zero => rfl
  | succ n ih => rw [codeWith,maskSubTritCode,row,ih]

abbrev Edge := Fin 6 × Fin 6

def present (mask : ℕ) (e : Edge) : ℕ := cond (adjBool mask e.1.val e.2.val) 1 0

def atom (e : Edge) (u v : Fin 6) : ℕ :=
  (if e = (u,v) then 1 else 0) + (if e = (v,u) then 2 else 0)

private theorem pair_sum (mask : ℕ) (u v : Fin 6) :
    (∑ e : Edge, present mask e * atom e u v) = pairTritBool mask u.val v.val := by
  simp only [atom, mul_add, mul_ite, mul_zero, mul_one, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold present pairTritBool
  dsimp only
  cases h : adjBool mask u.val v.val <;> cases h' : adjBool mask v.val u.val <;> try rfl
  exact False.elim ((maskGraph 6 mask).asymm u v h h')

/-- Slots 0–4 are the full code and its prefixes, 5–10 the six right flags,
and 11 the degree multiplier on positions 0,2,3,4,5. -/
def arity : ℕ → ℕ
  | 0 => 6 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 3
  | 6 => 4 | 7 => 5 | 8 => 3 | 9 => 4 | 10 => 3 | 11 => 5 | _ => 0

def vertex : ℕ → ℕ → ℕ
  | 5 => skip 0 3 | 6 => skip 2 2 | 7 => skip 4 1 | 8 => skip 1 2
  | 9 => skip 3 1 | 10 => skip 2 1 | 11 => skipSecond | _ => id

def order (p i : ℕ) : Fin 6 := ⟨pDigit (permutationAt permutationTable p) i % 6, Nat.mod_lt _ (by decide)⟩

def feature (mask p slot : ℕ) : ℕ :=
  maskSubTritCode mask (fun i => (order p (vertex slot i)).val) (arity slot)

def basis (e : Edge) (p slot : ℕ) : ℕ :=
  codeWith (fun i j => atom e (order p (vertex slot i)) (order p (vertex slot j))) (arity slot)

private theorem feature_sum (mask p slot : ℕ) :
    (∑ e : Edge, present mask e * basis e p slot) = feature mask p slot := by
  unfold basis feature
  rw [code_sum, show (fun i j => ∑ e : Edge, present mask e *
      atom e (order p (vertex slot i)) (order p (vertex slot j))) = _ from
      funext fun i => funext fun j => pair_sum mask _ _, code_mask]

private theorem feature_lt (mask p slot : ℕ) (hs : slot < 12) : feature mask p slot < 2^32 := by
  let n := arity slot
  let v (i : Fin n) := order p (vertex slot i.val)
  have eqn := graphTritCode_pullback_maskGraph mask v (fun j => (order p (vertex slot j)).val) (fun _ => rfl)
  have bound := graphTritCode_lt ((maskGraph 6 mask).pullback v)
  rw [eqn] at bound
  have hn : n ≤ 6 := by dsimp [n]; interval_cases slot <;> decide
  exact bound.trans_le (by interval_cases n <;> decide)

def bankIndex (i j batch : ℕ) : ℕ := Nat.add (Nat.mul (Nat.add (Nat.mul i 6) j) 45) batch

def checkBankEdge (bank : NTree) (i j : Fin 6) : Bool :=
  allBelow 45 fun batch =>
    Nat.beq (bank.get (bankIndex i.val j.val batch))
      (pack (2^384) (fun p => pack (2^32) (fun s => basis (i,j) (batch*16+p) s) 12 0) 16 0)

def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.add (sumN f n) (f n)

private theorem sumN_fin (f : ℕ → ℕ) (n : ℕ) : sumN f n = ∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => simp [sumN,Fin.sum_univ_castSucc,ih]

def batchData (bank : NTree) (mask batch : ℕ) : ℕ :=
  sumN (fun i => sumN (fun j => cond (adjBool mask i j) (bank.get (bankIndex i j batch)) 0) 6) 6

theorem batch_spec {bank : NTree} (hb : ∀ i j, checkBankEdge bank i j = true)
    (mask batch : ℕ) (hbatch : batch < 45) :
    batchData bank mask batch =
    pack (2^384) (fun p => pack (2^32) (feature mask (batch*16+p)) 12 0) 16 0 := by
  have sumForm : batchData bank mask batch =
      ∑ e : Edge, present mask e * bank.get (bankIndex e.1.val e.2.val batch) := by
    rw [Fintype.sum_prod_type]
    unfold batchData
    simp_rw [sumN_fin]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    cases h : adjBool mask i.val j.val <;> simp [present,h]
  rw [sumForm]
  have cell (e : Edge) : bank.get (bankIndex e.1.val e.2.val batch) =
      pack (2^384) (fun p => pack (2^32) (basis e (batch*16+p)) 12 0) 16 0 :=
    Nat.beq_eq.mp (of_allBelow (hb e.1 e.2) hbatch)
  simp_rw [cell]
  rw [pack_sum]
  apply pack_congr
  intro p _ _
  rw [pack_sum]
  exact pack_congr _ _ _ _ _ (fun slot _ _ => feature_sum mask _ slot)

set_option exponentiation.threshold 512 in
theorem frame_slot {bank : NTree} (hb : ∀ i j, checkBankEdge bank i j = true)
    (mask batch i slot : ℕ) (hbatch : batch < 45) (hi : i < 16) (hs : slot < 12) :
    lane 32 (lane 384 (batchData bank mask batch) i) slot = feature mask (batch*16+i) slot := by
  rw [batch_spec hb mask batch hbatch, lane_pack 384 _ 16 0 i hi]
  · simpa using lane_pack 32 (feature mask (batch*16+i)) 12 0 slot hs
      (fun j _ hj => feature_lt mask _ j (by omega))
  · intro p _ _
    have h := pack_lt (2^32) (by decide) (feature mask (batch*16+p)) 12 0
      (fun j _ hj => feature_lt mask _ j (by omega))
    exact h.trans_le (by decide)

/-- A checked frame supplies the frequent projections, with a general fallback
for layouts unused by the present certificates. -/
def unpackView (word : ℕ) (X : View) : View where
  arc i j := if i < 6 ∧ j < 6 then tritCodeAdj 6 (lane 32 word 0) i j else X.arc i j
  prefixCode k := match k with
    | 2 => lane 32 word 4 | 3 => lane 32 word 3 | 4 => lane 32 word 2
    | 5 => lane 32 word 1 | 6 => lane 32 word 0 | n => X.prefixCode n
  rightCode k d := match k,d with
    | 0,3 => lane 32 word 5 | 2,2 => lane 32 word 6 | 4,1 => lane 32 word 7
    | 1,2 => lane 32 word 8 | 3,1 => lane 32 word 9 | 2,1 => lane 32 word 10
    | a,b => X.rightCode a b
  degreeCode r := if r = 4 then lane 32 word 11 else X.degreeCode r

private theorem view_ext {X Y : View} (ha : X.arc = Y.arc) (hp : X.prefixCode = Y.prefixCode)
    (hr : X.rightCode = Y.rightCode) (hd : X.degreeCode = Y.degreeCode) : X = Y := by
  cases X; cases Y; congr

theorem unpack_eq {mask p word : ℕ} (h : ∀ slot < 12, lane 32 word slot = feature mask p slot) :
    unpackView word (rawView mask (fun i => (order p i).val)) = rawView mask (fun i => (order p i).val) := by
  let X := rawView mask (fun i => (order p i).val)
  suffices ha : (unpackView word X).arc = X.arc by
    have hp : (unpackView word X).prefixCode = X.prefixCode := by
      funext k
      simp only [unpackView]
      split <;> first | rfl | exact h _ (by decide)
    have hr : (unpackView word X).rightCode = X.rightCode := by
      funext k d
      simp only [unpackView]
      split <;> first | rfl | exact h _ (by decide)
    have hd : (unpackView word X).degreeCode = X.degreeCode := by
      funext r
      by_cases he : r=4
      · subst r
        simpa [unpackView, X, rawView, feature, vertex, arity] using h 11 (by decide)
      · simp only [unpackView,he,ite_false]
    exact view_ext ha hp hr hd
  funext i j
  by_cases hij : i<6 ∧ j<6
  · change (if _ then _ else _) = _
    rw [ite_eq_left hij,h 0 (by decide)]
    let K := (maskGraph 6 mask).pullback (fun v : Fin 6 => order p v.val)
    have hc : graphTritCode K = feature mask p 0 :=
      graphTritCode_pullback_maskGraph mask _ _ (fun _ => rfl)
    rw [← hc]
    apply Bool.eq_iff_iff.mpr
    exact (adj_iff_tritCodeAdj K ⟨i,hij.1⟩ ⟨j,hij.2⟩).symm
  · simp only [unpackView,hij,ite_false]

/-- Force a computed natural to a numeral before passing it to multiple lookups. -/
def withNat {T : Type} (n : ℕ) (f : ℕ → T) : T := Nat.casesOn n (f 0) (fun j => f (j+1))

theorem withNat_eq {T : Type} (n : ℕ) (f : ℕ → T) : withNat n f = f n := by cases n <;> rfl

def packedRow (bank : NTree) (ps : List (Piece 6)) (mask : ℕ) : ℤ × ℤ :=
  sumRows (fun b => withNat (batchData bank mask b) fun data =>
    sumRows (fun i => withNat (lane 384 data i) fun word =>
      let p := b*16+i
      evalPieces ps (unpackView word (rawView mask (fun j => (order p j).val)))) 16) 45

private theorem sumRows_range (f : ℕ → ℤ × ℤ) (n : ℕ) :
    (sumRows f n).1 = ∑ j ∈ Finset.range n, (f j).1 ∧
    (sumRows f n).2 = ∑ j ∈ Finset.range n, (f j).2 := by
  induction n with
  | zero => simp [sumRows]
  | succ n ih =>
    simp only [sumRows, Finset.sum_range_succ]
    exact ⟨congrArg (· + _) ih.1,congrArg (· + _) ih.2⟩

private theorem sum_blocks (f : ℕ → ℤ) (a b : ℕ) :
    (∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i*b+j)) = ∑ n ∈ Finset.range (a*b), f n := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul,Finset.sum_range_succ,Finset.sum_range_add,ih]

set_option maxRecDepth 4096 in
theorem packedRow_eq {bank : NTree} (hb : ∀ i j, checkBankEdge bank i j = true)
    (ps : List (Piece 6)) (mask : ℕ) :
    packedRow bank ps mask = modelRow (assemble ps) permutationTable mask := by
  rw [← groupedRow_eq]
  unfold packedRow groupedRow
  simp_rw [cached_eq]
  simp_rw [withNat_eq]
  let f (p : ℕ) := evalPieces ps (rawView mask (fun j => (order p j).val))
  have one (b : ℕ) (h : b<45) (i : ℕ) (hi : i<16) :
      evalPieces ps (unpackView (lane 384 (batchData bank mask b) i)
        (rawView mask (fun j => (order (b*16+i) j).val))) = f (b*16+i) := by
    rw [unpack_eq (fun s hs => frame_slot hb mask b i s h hi hs)]
  have grouped (b : ℕ) (h : b<45) :
      sumRows (fun i => evalPieces ps (unpackView (lane 384 (batchData bank mask b) i)
        (rawView mask (fun j => (order (b*16+i) j).val)))) 16 = sumRows (fun i => f (b*16+i)) 16 := by
    apply Prod.ext <;> first
    | rw [(sumRows_range _ _).1,(sumRows_range _ _).1]
      exact Finset.sum_congr rfl fun i hi => congrArg Prod.fst (one b h i (Finset.mem_range.mp hi))
    | rw [(sumRows_range _ _).2,(sumRows_range _ _).2]
      exact Finset.sum_congr rfl fun i hi => congrArg Prod.snd (one b h i (Finset.mem_range.mp hi))
  apply Prod.ext <;> first
  | rw [(sumRows_range _ _).1,(sumRows_range _ _).1]
    calc _ = ∑ b ∈ Finset.range 45, ∑ i ∈ Finset.range 16, (f (b*16+i)).1 := by
           exact Finset.sum_congr rfl fun b h => (congrArg Prod.fst (grouped b (Finset.mem_range.mp h))).trans (sumRows_range _ _).1
         _ = _ := sum_blocks (fun p => (f p).1) 45 16
  | rw [(sumRows_range _ _).2,(sumRows_range _ _).2]
    calc _ = ∑ b ∈ Finset.range 45, ∑ i ∈ Finset.range 16, (f (b*16+i)).2 := by
           exact Finset.sum_congr rfl fun b h => (congrArg Prod.snd (grouped b (Finset.mem_range.mp h))).trans (sumRows_range _ _).2
         _ = _ := sum_blocks (fun p => (f p).2) 45 16

def checkPackedSlice (bank : NTree) (ps : List (Piece 6)) (E : Endpoints) (start length : ℕ) : Bool :=
  checkRange (fun i => E.accepts (packedRow bank ps (models6Tree.get i))) start length

theorem of_checkPackedSlice {bank : NTree} (hb : ∀ i j, checkBankEdge bank i j = true)
    {ps : List (Piece 6)} {E : Endpoints} {start length i : ℕ}
    (h : checkPackedSlice bank ps E start length = true) (hl : start ≤ i) (hh : i < start+length) :
    E.accepts (modelRow (assemble ps) permutationTable (models6Tree.get i)) = true := by
  rw [← packedRow_eq hb]
  exact of_checkRange (f := fun j => E.accepts (packedRow bank ps (models6Tree.get j))) h hl hh

end CaccettaHaggkvist.SixVertex.Geometry
