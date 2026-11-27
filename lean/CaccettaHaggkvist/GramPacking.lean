module

public import CaccettaHaggkvist.CertificateGram

/-! # Exact row verification of Gram factorizations by Kronecker substitution

At radix b the residual coefficients have absolute value strictly below b.
Equality of the two signed row polynomials at b then implies coefficientwise
equality. This replaces a dot product for every matrix cell by a dot product
for every row and two inexpensive coefficient-bound scans.
-/

@[expose] public section

namespace CaccettaHaggkvist.CertificateGram

def polynomial (b : ℤ) : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n+1, f => f 0 + b * polynomial b n (fun j => f (j+1))

private theorem polynomial_ext {b : ℤ} (hb : 0 < b) (n : ℕ) (f g : ℕ → ℤ)
    (hbound : ∀ j < n, |f j - g j| < b) (h : polynomial b n f = polynomial b n g) :
    ∀ j < n, f j = g j := by
  induction n generalizing f g with
  | zero => intro j hj; omega
  | succ n ih =>
    let u := polynomial b n (fun j => f (j+1))
    let v := polynomial b n (fun j => g (j+1))
    change f 0 + b*u = g 0 + b*v at h
    obtain ⟨hl,hr⟩ := abs_lt.mp (hbound 0 (by omega))
    have huv : u = v := by
      rcases lt_trichotomy u v with hlt | eq | hgt
      · have hgap : 0 ≤ v-u-1 := by omega
        nlinarith [mul_nonneg hb.le hgap]
      · exact eq
      · have hgap : 0 ≤ u-v-1 := by omega
        nlinarith [mul_nonneg hb.le hgap]
    intro j hj
    cases j with
    | zero => rw [huv] at h; linarith
    | succ j =>
      exact ih (fun j => f (j+1)) (fun j => g (j+1))
        (fun j hj => hbound (j+1) (by omega)) huv j (by omega)

private theorem polynomial_dot (b : ℤ) (n rank : ℕ) (c : ℕ → ℤ) (f : ℕ → ℕ → ℤ) :
    polynomial b n (fun j => ∑ t ∈ Finset.range rank, c t * f t j) =
      ∑ t ∈ Finset.range rank, c t * polynomial b n (f t) := by
  induction n generalizing f with
  | zero => simp [polynomial]
  | succ n ih =>
    simp only [polynomial]
    rw [ih (fun t j => f t (j+1)), Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)

structure Packing where
  radix : ℕ
  factorBound : ℕ
  entryBound : ℕ
  packedFactor : ℕ → ℤ

def Packing.check (P : Packing) (B : CertificateGram) : Bool :=
  Nat.ble B.dim (2^17) &&
  decide ((P.entryBound : ℤ) + sumInt (fun t => (B.weight t : ℤ)) B.rank *
    (P.factorBound : ℤ)^2 < (P.radix : ℤ)) &&
  allBelow B.rank (fun t =>
    decide (P.packedFactor t = polynomial P.radix B.dim (B.factor t)) &&
    allBelow B.dim (fun i => decide (|B.factor t i| ≤ (P.factorBound : ℤ)))) &&
  allBelow B.dim (fun i =>
    allBelow B.dim (fun j => decide (|B.entry i j| ≤ (P.entryBound : ℤ))) &&
    decide (polynomial P.radix B.dim (B.entry i) =
      sumInt (fun t => (B.weight t : ℤ) * B.factor t i * P.packedFactor t) B.rank))

theorem Packing.sound (P : Packing) (B : CertificateGram) (h : P.check B = true) : B.check = true := by
  simp only [Packing.check, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hsize, hbase⟩, hfactor⟩, hmat⟩ := h
  rw [sumInt_eq] at hbase
  have hweight : 0 ≤ ∑ t ∈ Finset.range B.rank, (B.weight t : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hb : 0 < (P.radix : ℤ) := lt_of_le_of_lt
    (add_nonneg (Int.natCast_nonneg _) (mul_nonneg hweight (sq_nonneg _))) hbase
  have hf (t : ℕ) (ht : t < B.rank) := Bool.and_eq_true_iff.mp (of_allBelow hfactor ht)
  have hfBound (t i : ℕ) (ht : t < B.rank) (hi : i < B.dim) :
      |B.factor t i| ≤ (P.factorBound : ℤ) := of_decide_eq_true (of_allBelow (hf t ht).2 hi)
  unfold CertificateGram.check
  refine allBelow_eq_true_of_forall hsize fun i hi => ?_
  have row := Bool.and_eq_true_iff.mp (of_allBelow hmat hi)
  have eqn := of_decide_eq_true row.2
  rw [sumInt_eq] at eqn
  let coeff (j : ℕ) := ∑ t ∈ Finset.range B.rank,
    (B.weight t : ℤ) * B.factor t i * B.factor t j
  have polyEq : polynomial P.radix B.dim (B.entry i) = polynomial P.radix B.dim coeff := by
    rw [eqn, polynomial_dot (c := fun t => (B.weight t : ℤ) * B.factor t i) (f := B.factor)]
    exact Finset.sum_congr rfl (fun t ht => by rw [of_decide_eq_true (hf t (Finset.mem_range.mp ht)).1])
  refine allBelow_eq_true_of_forall hsize fun j hj => ?_
  apply decide_eq_true
  rw [sumInt_eq]
  apply polynomial_ext hb B.dim (B.entry i) coeff _ polyEq j hj
  intro l hl
  have bound : |coeff l| ≤ (∑ t ∈ Finset.range B.rank, (B.weight t : ℤ)) * (P.factorBound : ℤ)^2 := by
    unfold coeff
    rw [Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun t ht => ?_)
    have ht' := Finset.mem_range.mp ht
    rw [abs_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg _), mul_assoc, sq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hfBound t i ht' hi) (hfBound t l ht' hl) (abs_nonneg _) (Int.natCast_nonneg _))
      (Int.natCast_nonneg _)
  exact lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add
    (of_decide_eq_true (of_allBelow row.1 hl)) bound)) hbase

end CaccettaHaggkvist.CertificateGram
