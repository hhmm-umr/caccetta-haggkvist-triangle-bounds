module

public import CaccettaHaggkvist.CertM5Refined
public import CaccettaHaggkvist.Lexicographic

/-! # The one-third threshold at finite orders

The lexicographic product gives a vertex of out-degree at most
`cStar * (n - 1)`. Compare this with the integer ceiling of `n / 3`.
-/

@[expose] public section

namespace CaccettaHaggkvist

variable {V : Type*} [Fintype V] [Nonempty V]

/-- A rational supremum bound gives the one-third theorem whenever its
finite-order upper bound is strictly below the integer degree threshold. -/
theorem hasCycleLe3_of_third_of_order_rounding {p q : ℕ} (hq : 0 < q)
    (hc : cStar ≤ (p : ℝ) / q)
    (hround : p * Fintype.card V < q * ((Fintype.card V + 2) / 3) + p)
    (G : Digraph V) [dG : DecidableRel G.adj]
    (hd : ∀ v, Fintype.card V ≤ 3 * G.outDeg v) : G.HasCycleLe3 := by
  classical
  by_contra hno
  let H := G.toOrientedOfNotHasDigon (fun h => hno (Or.inl h))
  let _ : DecidableRel H.adj := dG
  have hH : H.TriangleFree := fun h => hno (Or.inr h)
  obtain ⟨v, hv⟩ := H.exists_outDeg_le_pred_of_cStar_le hH hc
  change (G.outDeg v : ℝ) ≤ (p : ℝ) / q * ((Fintype.card V : ℝ) - 1) at hv
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hreal : (q : ℝ) * (G.outDeg v : ℝ) + p ≤ (p : ℝ) * Fintype.card V := calc
    _ ≤ (q : ℝ) * ((p : ℝ) / q * ((Fintype.card V : ℝ) - 1)) + p :=
      add_le_add_left (mul_le_mul_of_nonneg_left hv hq'.le) _
    _ = _ := by
      field_simp
      ring
  have hnat : q * G.outDeg v + p ≤ p * Fintype.card V := by exact_mod_cast hreal
  have hceil : (Fintype.card V + 2) / 3 ≤ G.outDeg v := by have := hd v; omega
  exact (not_le_of_gt hround) ((Nat.add_le_add_right (Nat.mul_le_mul_left q hceil) p).trans hnat)

/-- The closed five-vertex bound implies the one-third threshold through
order 41, through 121 in residue 1, and through 80 in residue 2 modulo 3. -/
theorem hasCycleLe3_of_third_of_five_vertex_order
    (hn : Fintype.card V ≤ 41 ∨ (Fintype.card V % 3 = 1 ∧ Fintype.card V ≤ 121) ∨
      (Fintype.card V % 3 = 2 ∧ Fintype.card V ≤ 80))
    (G : Digraph V) [DecidableRel G.adj]
    (hd : ∀ v, Fintype.card V ≤ 3 * G.outDeg v) : G.HasCycleLe3 := by
  have bounds : ∀ m : Fin 122, (m.val ≤ 41 ∨ (m.val % 3 = 1 ∧ m.val ≤ 121) ∨
      (m.val % 3 = 2 ∧ m.val ≤ 80)) →
      3415403 * m.val < 10000000 * ((m.val + 2) / 3) + 3415403 := by decide +kernel
  exact hasCycleLe3_of_third_of_order_rounding (by decide) cStar_le_3415403_10000000
    (bounds ⟨Fintype.card V, by omega⟩ hn) G hd

/-- Specializing the rounding argument at the externally checked six-vertex
bound gives all orders through 71, plus the two longer residue ranges. -/
theorem hasCycleLe3_of_third_of_six_vertex_order (hc : cStar ≤ (33823 / 100000 : ℝ))
    (hn : Fintype.card V ≤ 71 ∨ (Fintype.card V % 3 = 1 ∧ Fintype.card V ≤ 205) ∨
      (Fintype.card V % 3 = 2 ∧ Fintype.card V ≤ 137))
    (G : Digraph V) [DecidableRel G.adj]
    (hd : ∀ v, Fintype.card V ≤ 3 * G.outDeg v) : G.HasCycleLe3 := by
  have bounds : ∀ m : Fin 206, (m.val ≤ 71 ∨ (m.val % 3 = 1 ∧ m.val ≤ 205) ∨
      (m.val % 3 = 2 ∧ m.val ≤ 137)) →
      33823 * m.val < 100000 * ((m.val + 2) / 3) + 33823 := by decide +kernel
  exact hasCycleLe3_of_third_of_order_rounding (by decide) hc
    (bounds ⟨Fintype.card V, by omega⟩ hn) G hd

end CaccettaHaggkvist
