module

public import CaccettaHaggkvist.ExtremalBridge

/-! # Finite-order correction to a triangle-free minimum out-degree bound

Substitution into a graph by near-extremizers improves the factor multiplying
the global ratio from the order to the order minus one.
-/

@[expose] public section

namespace CaccettaHaggkvist.OrientedGraph

universe u v

def lex {V : Type u} {W : Type v} (G : OrientedGraph V) (H : OrientedGraph W) :
    OrientedGraph (V × W) where
  adj x y := G.adj x.1 y.1 ∨ (x.1 = y.1 ∧ H.adj x.2 y.2)
  loopless x := fun h => h.elim (G.loopless _) (fun hi => H.loopless _ hi.2)
  asymm x y hxy hyx := by
    rcases hxy with ho | ⟨he, hi⟩ <;> rcases hyx with hr | ⟨hr, hj⟩
    · exact G.asymm _ _ ho hr
    · exact G.loopless _ (hr ▸ ho)
    · exact G.loopless _ (he ▸ hr)
    · exact H.asymm _ _ hi hj

instance {V : Type u} {W : Type v} [DecidableEq V] (G : OrientedGraph V) (H : OrientedGraph W)
    [DecidableRel G.adj] [DecidableRel H.adj] : DecidableRel (G.lex H).adj := fun x y =>
  inferInstanceAs (Decidable (G.adj x.1 y.1 ∨ (x.1 = y.1 ∧ H.adj x.2 y.2)))

theorem triangleFree_lex {V : Type u} {W : Type v} {G : OrientedGraph V} {H : OrientedGraph W}
    (hG : G.TriangleFree) (hH : H.TriangleFree) : (G.lex H).TriangleFree := by
  rintro ⟨⟨a,i⟩, ⟨b,j⟩, ⟨c,k⟩, hab, hbc, hca⟩
  change G.adj a b ∨ (a = b ∧ H.adj i j) at hab
  change G.adj b c ∨ (b = c ∧ H.adj j k) at hbc
  change G.adj c a ∨ (c = a ∧ H.adj k i) at hca
  by_cases ab : a = b
  · subst b
    have hij := (hab.resolve_left (G.loopless _)).2
    by_cases ac : a = c
    · subst c
      exact hH ⟨i, j, k, hij, (hbc.resolve_left (G.loopless _)).2,
        (hca.resolve_left (G.loopless _)).2⟩
    · exact G.asymm _ _ (hbc.resolve_right fun h => ac h.1)
        (hca.resolve_right fun h => ac h.1.symm)
  · have eab := hab.resolve_right fun h => ab h.1
    rcases hbc with ebc | ⟨rfl, _⟩
    · rcases hca with eca | ⟨rfl, _⟩
      · exact hG ⟨a,b,c,eab,ebc,eca⟩
      · exact G.asymm _ _ eab ebc
    · exact G.asymm _ _ eab (hca.resolve_right fun h => ab h.1.symm)

theorem outDeg_lex {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : OrientedGraph V) (H : OrientedGraph W)
    [DecidableRel G.adj] [DecidableRel H.adj] (a : V) (i : W) :
    (G.lex H).toDigraph.outDeg (a,i) =
      G.toDigraph.outDeg a * Fintype.card W + H.toDigraph.outDeg i := by
  let outer := G.toDigraph.outSet a ×ˢ (Finset.univ : Finset W)
  let inner := ({a} : Finset V) ×ˢ H.toDigraph.outSet i
  have hset : (G.lex H).toDigraph.outSet (a,i) = outer ∪ inner := by
    ext ⟨b,j⟩
    rw [Digraph.mem_outSet]
    change G.adj a b ∨ a = b ∧ H.adj i j ↔ _
    simp [outer, inner, eq_comm, and_comm]
  have hdis : Disjoint outer inner := by
    rw [Finset.disjoint_left]
    rintro ⟨b,j⟩ ho hi
    have hb : b = a := Finset.mem_singleton.mp (Finset.mem_product.mp hi).1
    have hab : G.adj a b := (Digraph.mem_outSet G.toDigraph).mp (Finset.mem_product.mp ho).1
    exact G.loopless a (hb ▸ hab)
  change ((G.lex H).toDigraph.outSet (a,i)).card = _
  rw [hset, Finset.card_union_of_disjoint hdis]
  simp [outer, inner, Digraph.outDeg]

/-- Every lower bound `d` on the out-degrees of a nonempty triangle-free
oriented graph satisfies `d ≤ cStar * (n - 1)`. -/
theorem minOutDeg_le_cStar_card_sub_one {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : OrientedGraph V) [DecidableRel G.adj] (hG : G.TriangleFree)
    (d : ℕ) (hd : ∀ v, d ≤ G.toDigraph.outDeg v) :
    (d : ℝ) ≤ cStar * ((Fintype.card V : ℝ) - 1) := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have bound : cStar ≤ cStar * Fintype.card V - d := by
    refine csSup_le c3FreeRatios_nonempty fun r hr => ?_
    obtain ⟨m, hm, H, decH, hH, hdeg⟩ := hr
    let _ : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    let _ : DecidableRel H.adj := decH
    have hprod : ((d : ℝ) + r) / Fintype.card V ≤ cStar := by
      apply le_cStar_of_orientedGraph (G.lex H) (triangleFree_lex hG hH)
      rintro ⟨a,i⟩
      rw [outDeg_lex, Fintype.card_prod, Fintype.card_fin]
      push_cast
      calc
        ((d : ℝ) + r) / Fintype.card V * (Fintype.card V * (m : ℝ)) =
          (d : ℝ) * m + r * m := by field_simp
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (hd a)) (Nat.cast_nonneg m)) (hdeg i)
    linarith [(div_le_iff₀ hn).mp hprod]
  linarith

theorem exists_outDeg_le_pred_of_cStar_le {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : OrientedGraph V) [DecidableRel G.adj] (hG : G.TriangleFree) {c : ℝ} (hc : cStar ≤ c) :
    ∃ v : V, (G.toDigraph.outDeg v : ℝ) ≤ c*((Fintype.card V : ℝ)-1) := by
  obtain ⟨v, _, hv⟩ := Finset.exists_min_image Finset.univ G.toDigraph.outDeg Finset.univ_nonempty
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos
  have hnon : (0 : ℝ) ≤ (Fintype.card V : ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hn)
  exact ⟨v, (G.minOutDeg_le_cStar_card_sub_one hG _ (fun z => hv z (Finset.mem_univ z))).trans
    (mul_le_mul_of_nonneg_right hc hnon)⟩

end CaccettaHaggkvist.OrientedGraph

namespace CaccettaHaggkvist

/-- A non-strict upper bound on the supremum gives the strict finite-degree conclusion. -/
theorem hasCycleLe3_of_cStar_le {c : ℝ} (hc : cStar ≤ c) (hpos : 0 < c)
    {V : Type*} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj]
    (hd : ∀ v, c * Fintype.card V ≤ (G.outDeg v : ℝ)) : G.HasCycleLe3 := by
  apply hasCycleLe3_of_oriented_bound (c := c) _ G hd
  intro H decH hH
  classical
  let _ : DecidableRel H.adj := decH
  obtain ⟨v,h⟩ := H.exists_outDeg_le_pred_of_cStar_le hH hc
  exact ⟨v, lt_of_le_of_lt h (by linarith)⟩

end CaccettaHaggkvist
