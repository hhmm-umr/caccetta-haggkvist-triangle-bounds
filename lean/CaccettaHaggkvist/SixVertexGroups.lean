module

public import CaccettaHaggkvist.SixVertexFast

/-! # Block-diagonal flag kernels

A flag selects its own block. If the two flags select different blocks their
bilinear coefficient vanishes. Selection may be any function of a single flag,
so it can use the leading digits of the rooted subgraph code.
-/

@[expose] public section

namespace CaccettaHaggkvist.SixVertex

def addPair (a b : ℤ × ℤ) : ℤ × ℤ := (a.1+b.1,a.2+b.2)

private theorem add_zero (a : ℤ × ℤ) : addPair a (0,0) = a := by simp [addPair]
private theorem zero_add (a : ℤ × ℤ) : addPair (0,0) a = a := by simp [addPair]

def foldView {m : ℕ} (ts : List (Term m)) (X : View) : ℤ × ℤ :=
  ts.foldr (fun t z => addPair (t.fast X) z) (0,0)

private theorem fold_append {m : ℕ} (a b : List (Term m)) (X : View) :
    foldView (a++b) X = addPair (foldView a X) (foldView b X) := by
  induction a with
  | nil => exact (zero_add _).symm
  | cons t as ih =>
    change addPair _ (foldView (as++b) X) = addPair (addPair _ (foldView as X)) _
    rw [ih]; simp [addPair,Int.add_assoc]

structure BlockGroup where
  blocks : List CertificateGram
  select : ℕ → ℕ

def BlockGroup.block (G : BlockGroup) (i : ℕ) : CertificateGram :=
  G.blocks[i]?.getD ⟨0,0,fun _ => 0,fun _ => 0,fun _ _ => 0,fun _ _ => 0⟩

def BlockGroup.tagged (G : BlockGroup) (i : ℕ) : CertificateGram :=
  let B := G.block i
  {B with flagId := fun l => if G.select l = i then B.flagId l else B.dim}

private theorem taggedValue (G : BlockGroup) (i l r : ℕ) :
    (G.tagged i).value l r = if G.select l = i ∧ G.select r = i then
      (G.block i).value l r else 0 := by
  by_cases hl : G.select l = i <;> by_cases hr : G.select r = i <;>
    simp [BlockGroup.tagged, CertificateGram.value,hl,hr]

def groupTerms (k d e : ℕ) (L : Local k e) (G : BlockGroup) : ℕ → List (Term (k+d+d+e))
  | 0 => []
  | n+1 => .gram k d e L (G.tagged n) :: groupTerms k d e L G n

def groupEval (k d e : ℕ) (L : Local k e) (G : BlockGroup) (n : ℕ) (X : View) : ℤ × ℤ :=
  let a := G.select (X.prefixCode (k+d))
  let b := G.select (X.rightCode k d)
  if a < n ∧ a = b then (Term.gram k d e L (G.block a)).fast X else (0,0)

theorem groupEval_eq (k d e : ℕ) (L : Local k e) (G : BlockGroup) (n : ℕ) (X : View) :
    foldView (groupTerms k d e L G n) X = groupEval k d e L G n X := by
  let a := G.select (X.prefixCode (k+d))
  let b := G.select (X.rightCode k d)
  have step (i : ℕ) : (Term.gram k d e L (G.tagged i)).fast X =
      if a=i ∧ b=i then (Term.gram k d e L (G.block i)).fast X else (0,0) := by
    dsimp only [a,b]
    by_cases h : G.select (X.prefixCode (k+d)) = i ∧ G.select (X.rightCode k d) = i <;>
      simp [Term.fast,taggedValue,h]
  induction n with
  | zero => simp [foldView,groupTerms,groupEval]
  | succ n ih =>
    change addPair ((Term.gram k d e L (G.tagged n)).fast X) (foldView _ X) = _
    rw [step, ih]
    change addPair (if a=n ∧ b=n then _ else _) (if a<n ∧ a=b then _ else _) =
      if a<n+1 ∧ a=b then _ else _
    by_cases h : a=b
    · rw [← h]
      rcases lt_trichotomy a n with ha | ha | ha
      · simp [Nat.ne_of_lt ha, ha, Nat.lt_succ_of_lt ha, zero_add]
      · have hsel : G.select (X.prefixCode (k+d)) = n := ha
        simp [ha,hsel,add_zero]
      · have hn : ¬ a < n+1 := by omega
        simp [Nat.ne_of_gt ha, Nat.not_lt_of_gt ha, hn, zero_add]
    · have hne : ¬ (a=n ∧ b=n) := fun z => h (z.1.trans z.2.symm)
      simp [h,hne,zero_add]

inductive Piece : ℕ → Type
  | single {m : ℕ} (t : Term m) : Piece m
  | grouped (k d e : ℕ) (L : Local k e) (G : BlockGroup) : Piece (k+d+d+e)

def Piece.terms {m : ℕ} : Piece m → List (Term m)
  | .single t => [t]
  | .grouped k d e L G => groupTerms k d e L G G.blocks.length

def Piece.fast {m : ℕ} : Piece m → View → ℤ × ℤ
  | .single t, X => t.fast X
  | .grouped k d e L G, X => groupEval k d e L G G.blocks.length X

def Piece.check {m : ℕ} : Piece m → Bool
  | .single t => t.check
  | .grouped _ _ _ _ G => G.blocks.all CertificateGram.check

private theorem groupChecks (k d e : ℕ) (L : Local k e) (G : BlockGroup)
    (h : G.blocks.all CertificateGram.check = true) (n : ℕ) (hn : n ≤ G.blocks.length) :
    (groupTerms k d e L G n).all Term.check = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_,ih (by omega)⟩
    have hi : n < G.blocks.length := by omega
    change (G.block n).check = true
    simpa [BlockGroup.block, List.getElem?_eq_getElem hi] using
      List.all_eq_true.mp h G.blocks[n] (List.getElem_mem hi)

private theorem piece_checked {m : ℕ} (p : Piece m) (h : p.check = true) :
    p.terms.all Term.check = true := by
  cases p with
  | single t => exact Bool.and_eq_true_iff.mpr ⟨h,rfl⟩
  | grouped k d e L G => exact groupChecks k d e L G h _ le_rfl

private theorem piece_value {m : ℕ} (p : Piece m) (X : View) :
    p.fast X = foldView p.terms X := by
  cases p with
  | single t => exact (add_zero _).symm
  | grouped k d e L G => exact (groupEval_eq k d e L G _ X).symm

def assemble (ps : List (Piece 6)) : Program := ps.flatMap Piece.terms

theorem assemble_checked (ps : List (Piece 6)) (h : ps.all Piece.check = true) :
    (assemble ps).check = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨hp,hs⟩ := Bool.and_eq_true_iff.mp h
    have hfirst := piece_checked p hp
    simp only [assemble, Program.check, List.flatMap_cons, List.all_append, hfirst, Bool.true_and]
    exact ih hs

def evalPieces (ps : List (Piece 6)) (X : View) : ℤ × ℤ :=
  ps.foldr (fun p b => addPair (p.fast X) b) (0,0)

theorem evalPieces_eq (ps : List (Piece 6)) (X : View) :
    evalPieces ps X = (assemble ps).fast X := by
  change _ = foldView (assemble ps) X
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change addPair (p.fast X) (evalPieces ps X) = foldView (p.terms ++ assemble ps) X
    rw [fold_append, ih]
    rw [piece_value]

def groupedRow (ps : List (Piece 6)) (table mask : ℕ) : ℤ × ℤ :=
  sumRows (fun i =>
    let p := permutationAt table i
    let v := fun j => Nat.mod (pDigit p j) 6
    evalPieces ps (cached (rawView mask v))) 720

theorem groupedRow_eq (ps : List (Piece 6)) (table mask : ℕ) :
    groupedRow ps table mask = modelRow (assemble ps) table mask := by
  rw [← fastModelRow_eq]
  unfold groupedRow fastModelRow
  congr 1
  funext i
  exact evalPieces_eq ps _

def checkGroupedSlice (ps : List (Piece 6)) (E : Endpoints) (table start length : ℕ) : Bool :=
  checkRange (fun i => E.accepts (groupedRow ps table (models6Tree.get i))) start length

theorem of_checkGroupedSlice {ps : List (Piece 6)} {E : Endpoints} {table start length i : ℕ}
    (h : checkGroupedSlice ps E table start length = true) (hl : start ≤ i) (hh : i < start+length) :
    E.accepts (modelRow (assemble ps) table (models6Tree.get i)) = true := by
  rw [← groupedRow_eq]
  exact of_checkRange (f := fun j => E.accepts (groupedRow ps table (models6Tree.get j))) h hl hh

end CaccettaHaggkvist.SixVertex
