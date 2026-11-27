module

public import CaccettaHaggkvist.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Rainbow triangles from a directed-triangle bound

The argument follows the reduction of Hompe, Qu and Spirkl. The theorem
`rainbow_triangle_of_ch_bound` takes a bound on the minimum out-degree of
directed-triangle-free oriented graphs as a hypothesis. The three numerical
specializations below retain that hypothesis. The unconditional specialization
using the five-vertex certificate is in `RainbowBounds`.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u v

/-! ## Section 1: Simple Edge-Colored Graphs & Rainbow Triangles -/

/-- A simple undirected edge-colored graph on vertex type `V` with color type `C`.
`adj` is irreflexive and symmetric (no loops, no parallel edges), and `color` is symmetric. -/
structure EdgeColoredGraph (V : Type u) (C : Type v) where
  adj : V → V → Prop
  loopless : ∀ x, ¬ adj x x
  symm : ∀ x y, adj x y → adj y x
  color : V → V → C
  color_symm : ∀ x y, color x y = color y x

namespace EdgeColoredGraph

variable {V : Type u} {C : Type v}

lemma ne_of_adj (G : EdgeColoredGraph V C) {x y : V} (h : G.adj x y) : x ≠ y := by
  rintro rfl; exact G.loopless x h

/-- `G` contains a rainbow triangle: three vertices forming a triangle whose three edges have
pairwise distinct colors. -/
def HasRainbowTriangle (G : EdgeColoredGraph V C) : Prop :=
  ∃ x y z : V,
    G.adj x y ∧ G.adj y z ∧ G.adj z x ∧
    G.color x y ≠ G.color y z ∧ G.color y z ≠ G.color z x ∧ G.color z x ≠ G.color x y

section ClassicalEdges
open Classical

/-- Set of undirected edges of `G` (as unordered pairs in `Sym2 V`). -/
noncomputable def edgeFinset [Fintype V] [DecidableEq V] (G : EdgeColoredGraph V C) :
    Finset (Sym2 V) :=
  Finset.univ.filter (Sym2.lift ⟨G.adj, fun _ _ => propext ⟨G.symm _ _, G.symm _ _⟩⟩)

/-- Set of undirected edges of `G` having color `c` (as unordered pairs in `Sym2 V`). -/
noncomputable def colorEdges [Fintype V] [DecidableEq V]
    (G : EdgeColoredGraph V C) (c : C) : Finset (Sym2 V) :=
  G.edgeFinset.filter (Sym2.lift ⟨fun x y => G.color x y = c,
    fun x y => by dsimp only; rw [G.color_symm x y]⟩)

@[simp]
lemma mem_edgeFinset_mk [Fintype V] [DecidableEq V] (G : EdgeColoredGraph V C)
    {x y : V} : s(x, y) ∈ G.edgeFinset ↔ G.adj x y := by
  unfold edgeFinset
  rw [Finset.mem_filter]
  simp

@[simp]
lemma mem_colorEdges_mk [Fintype V] [DecidableEq V]
    (G : EdgeColoredGraph V C) {c : C} {x y : V} :
    s(x, y) ∈ G.colorEdges c ↔ G.adj x y ∧ G.color x y = c := by
  unfold colorEdges
  rw [Finset.mem_filter, mem_edgeFinset_mk]
  simp

lemma colorEdges_subset [Fintype V] [DecidableEq V]
    (G : EdgeColoredGraph V C) (c : C) :
    G.colorEdges c ⊆ G.edgeFinset := by
  unfold colorEdges
  exact Finset.filter_subset _ _

end ClassicalEdges

lemma disjoint_colorEdges [Fintype V] [DecidableEq V]
    (G : EdgeColoredGraph V C) {c₁ c₂ : C} (hne : c₁ ≠ c₂) :
    Disjoint (G.colorEdges c₁) (G.colorEdges c₂) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_colorEdges_mk] at h1 h2
    exact hne (h1.2.symm.trans h2.2)

end EdgeColoredGraph

/-! ## Section 2: Elementary Simple Graph Counting (Goodman 1959 & 6-Line Zero-DP Happy-Triple Lemma) -/

section GraphCounting

open Classical in
private lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  have hd : Disjoint (s.filter p) (s.filter fun x => ¬ p x) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hu : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter]; by_cases h : p x <;> simp [h]
  rw [← Finset.card_union_of_disjoint hd, hu]

private lemma card_pair_diff {α : Type*} [DecidableEq α] (S : Finset α) :
    ((S ×ˢ S).filter fun p : α × α => p.1 ≠ p.2).card = S.card * (S.card - 1) := by
  have hdiag : ((S ×ˢ S).filter fun p : α × α => ¬ (p.1 ≠ p.2)).card = S.card := by
    refine Finset.card_bij (fun p _ => p.1)
      (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
      (fun p₁ hp₁ p₂ hp₂ heq => by
        have h1 : p₁.1 = p₁.2 := not_not.mp (Finset.mem_filter.mp hp₁).2
        have h2 : p₂.1 = p₂.2 := not_not.mp (Finset.mem_filter.mp hp₂).2
        exact Prod.ext heq (h1.symm.trans (heq.trans h2)))
      (fun x hx => ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, not_not.mpr rfl⟩, rfl⟩)
  have htot := card_filter_add_not (S ×ˢ S) (fun p : α × α => p.1 ≠ p.2)
  rw [hdiag, Finset.card_product] at htot
  cases h : S.card with
  | zero => rw [h] at htot; omega
  | succ m => rw [h] at htot; simp only [Nat.add_sub_cancel]; nlinarith

variable {V : Type u} [Fintype V] [DecidableEq V]

private def hasEdge (E : Finset (Sym2 V)) (x y : V) : Prop :=
  x ≠ y ∧ s(x, y) ∈ E

private instance instDecHasEdge (E : Finset (Sym2 V)) : DecidableRel (hasEdge E) :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ s(x, y) ∈ E))

omit [Fintype V] [DecidableEq V] in
private lemma hasEdge_symm {E : Finset (Sym2 V)} {x y : V} :
    hasEdge E x y ↔ hasEdge E y x := by
  unfold hasEdge; rw [ne_comm, Sym2.eq_swap]

private def degE (E : Finset (Sym2 V)) (x : V) : ℕ :=
  (Finset.univ.filter fun y => hasEdge E x y).card

private lemma card_incident_edges (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag) (v : V) :
    (E.filter fun e => v ∈ e).card = degE E v := by
  symm
  refine Finset.card_bij (fun y _ => s(v, y))
    (fun y hy => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).2.2, Sym2.mem_mk_left v y⟩)
    (fun y₁ hy₁ y₂ hy₂ heq => by
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact ((Finset.mem_filter.mp hy₂).2.1 h).elim)
    (fun e he => by
      rcases Finset.mem_filter.mp he with ⟨heE, hve⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hve
      have hne : v ≠ y := fun h => hloop _ heE (by subst h; exact Sym2.mk_isDiag_iff.mpr rfl)
      exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, heE⟩, rfl⟩)

private lemma sym2_card_double (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    ∑ x : V, degE E x = 2 * E.card := by
  let P : Finset (V × V) := Finset.univ.filter fun p : V × V => hasEdge E p.1 p.2
  have h1 : ∑ x : V, degE E x = P.card := by
    simp only [P, degE, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  rw [h1]
  have hfib : P.card = ∑ e ∈ E, (P.filter fun p => s(p.1, p.2) = e).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨x, y⟩
      rw [Finset.mem_biUnion]
      constructor
      · intro h
        have h' := (Finset.mem_filter.mp h).2
        exact ⟨s(x, y), h'.2, Finset.mem_filter.mpr ⟨h, rfl⟩⟩
      · rintro ⟨_, _, h⟩; exact (Finset.mem_filter.mp h).1
    · intro e₁ _ e₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact hne ((Finset.mem_filter.mp hp1).2.symm.trans (Finset.mem_filter.mp hp2).2)
  rw [hfib]
  have h2 : ∀ e ∈ E, (P.filter fun p => s(p.1, p.2) = e).card = 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hne : x ≠ y := fun h => hloop s(x, y) he (by subst h; exact Sym2.mk_isDiag_iff.mpr rfl)
      have hset : P.filter (fun p => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
        ext ⟨a, b⟩
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩; rw [Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        · rintro (h | h)
          · injection h with ha hb; subst ha; subst hb
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, he⟩, rfl⟩
          · injection h with ha hb; subst ha; subst hb
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne.symm, by rw [Sym2.eq_swap]; exact he⟩,
              Sym2.eq_swap⟩
      rw [hset, Finset.card_pair]
      intro h; exact hne (congrArg Prod.fst h)
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

private def ordTriangles (E : Finset (Sym2 V)) : ℕ :=
  (Finset.univ.filter fun t : V × V × V =>
    hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1).card

/-- **Goodman's Theorem (1959)** in exact ordered-triple form:
`n * ordTriangles E ≥ 8 * m * (m - n²/4)` (equivalently `t(G) ≥ (4m / 3n)(m - n²/4)`). -/
private lemma goodman_ordTriangles (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    (8 : ℝ) * (E.card : ℝ) * ((E.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4) ≤
      (Fintype.card V : ℝ) * (ordTriangles E : ℝ) := by
  let n : ℝ := (Fintype.card V : ℝ)
  let m : ℝ := (E.card : ℝ)
  have hsum_deg : ∑ x : V, (degE E x : ℝ) = 2 * m := by
    have hnat := sym2_card_double E hloop
    have hcast : ((∑ x : V, degE E x : ℕ) : ℝ) = ((2 * E.card : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast; exact hcast
  have hedge_cn : ∀ x y : V, hasEdge E x y →
      (degE E x : ℝ) + (degE E y : ℝ) - n ≤
        ((Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z).card : ℝ) := by
    intro x y _
    let Nx := Finset.univ.filter fun z : V => hasEdge E x z
    let Ny := Finset.univ.filter fun z : V => hasEdge E y z
    have hu := Finset.card_union_add_card_inter Nx Ny
    have hle : (Nx ∪ Ny).card ≤ Fintype.card V := Finset.card_le_univ _
    have hinter : Nx ∩ Ny = Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z := by
      ext z; simp [Nx, Ny]
    rw [hinter] at hu
    have hnat : degE E x + degE E y ≤
        Fintype.card V + (Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z).card := by
      change Nx.card + Ny.card ≤ _; omega
    have hreal : ((degE E x + degE E y : ℕ) : ℝ) ≤
        ((Fintype.card V + (Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal; linarith
  have htri_sum : (ordTriangles E : ℝ) =
      ∑ x : V, ∑ y : V, if hasEdge E x y then
        ((Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z).card : ℝ) else 0 := by
    have hnat : ordTriangles E = ∑ x : V, ∑ y : V, if hasEdge E x y then
        (Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z).card else 0 := by
      unfold ordTriangles
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hxy : hasEdge E x y
      · simp only [hxy, true_and, ↓reduceIte, Finset.card_eq_sum_ones, Finset.sum_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [hasEdge_symm (x := z) (y := x), and_comm]
      · simp [hxy]
    have hcast : (ordTriangles E : ℝ) = ((∑ x : V, ∑ y : V, if hasEdge E x y then
        (Finset.univ.filter fun z : V => hasEdge E x z ∧ hasEdge E y z).card else 0 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [hcast]
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hdeg2 : ∑ x : V, ∑ y : V, (if hasEdge E x y then ((degE E x : ℝ) + (degE E y : ℝ) - n) else 0) =
      2 * (∑ x : V, (degE E x : ℝ) ^ 2) - 2 * m * n := by
    have hs1 : ∑ x : V, ∑ y : V, (if hasEdge E x y then (degE E x : ℝ) else 0) =
        ∑ x : V, (degE E x : ℝ) ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      change (degE E x : ℝ) * (degE E x : ℝ) = _; ring
    have hs2 : ∑ x : V, ∑ y : V, (if hasEdge E x y then (degE E y : ℝ) else 0) =
        ∑ y : V, (degE E y : ℝ) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp_rw [hasEdge_symm (y := y)]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      change (degE E y : ℝ) * (degE E y : ℝ) = _; ring
    have hs3 : ∑ x : V, ∑ y : V, (if hasEdge E x y then n else 0) = 2 * m * n := by
      have : ∀ x : V, ∑ y : V, (if hasEdge E x y then n else 0) = (degE E x : ℝ) * n := by
        intro x; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; rfl
      simp_rw [this, ← Finset.sum_mul, hsum_deg]
    have hsplit : ∑ x : V, ∑ y : V, (if hasEdge E x y then ((degE E x : ℝ) + (degE E y : ℝ) - n) else 0) =
        (∑ x : V, ∑ y : V, if hasEdge E x y then (degE E x : ℝ) else 0) +
        (∑ x : V, ∑ y : V, if hasEdge E x y then (degE E y : ℝ) else 0) -
        (∑ x : V, ∑ y : V, if hasEdge E x y then n else 0) := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    rw [hsplit, hs1, hs2, hs3]; ring
  have hlb1 : 2 * (∑ x : V, (degE E x : ℝ) ^ 2) - 2 * m * n ≤ (ordTriangles E : ℝ) := by
    rw [← hdeg2, htri_sum]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    by_cases hxy : hasEdge E x y
    · simp only [hxy, ↓reduceIte]; exact hedge_cn x y hxy
    · simp [hxy]
  have hcs : (2 * m) ^ 2 ≤ n * ∑ x : V, (degE E x : ℝ) ^ 2 := by
    have hnn : 0 ≤ ∑ x : V, ∑ y : V, ((degE E x : ℝ) - (degE E y : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
    have hexp : ∑ x : V, ∑ y : V, ((degE E x : ℝ) - (degE E y : ℝ)) ^ 2 =
        2 * n * (∑ x : V, (degE E x : ℝ) ^ 2) - 2 * (∑ x : V, (degE E x : ℝ)) ^ 2 := by
      have h1 : ∀ x y : V, ((degE E x : ℝ) - (degE E y : ℝ)) ^ 2 =
          (degE E x : ℝ) ^ 2 - 2 * (degE E x : ℝ) * (degE E y : ℝ) + (degE E y : ℝ) ^ 2 :=
        fun _ _ => by ring
      have h2 : ∑ x : V, ∑ y : V, (2 * (degE E x : ℝ) * (degE E y : ℝ)) =
          2 * (∑ x : V, (degE E x : ℝ)) ^ 2 := by
        have : ∀ x : V, ∑ y : V, (2 * (degE E x : ℝ) * (degE E y : ℝ)) =
            (2 * (degE E x : ℝ)) * (∑ y : V, (degE E y : ℝ)) := fun x => by
          rw [Finset.mul_sum]
        simp_rw [this, ← Finset.sum_mul, ← Finset.mul_sum]; ring
      have h3 : ∑ x : V, ∑ _y : V, (degE E x : ℝ) ^ 2 = n * ∑ x : V, (degE E x : ℝ) ^ 2 := by
        simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]; rfl
      have h4 : ∑ _x : V, ∑ y : V, (degE E y : ℝ) ^ 2 = n * ∑ y : V, (degE E y : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2, h3, h4]
      ring
    rw [hexp, hsum_deg] at hnn
    linarith
  have hn_nn : 0 ≤ n := Nat.cast_nonneg _
  nlinarith

private def ordHappyTriples (E : Finset (Sym2 V)) : ℕ :=
  (Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧
    ((hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2) ∨
     (hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1) ∨
     (hasEdge E t.2.2 t.1 ∧ hasEdge E t.1 t.2.1))).card

private lemma ordHappyTriples_le_three_sum_deg_mul (E : Finset (Sym2 V)) :
    ordHappyTriples E ≤ 3 * ∑ x : V, degE E x * (degE E x - 1) := by
  let S₁ := Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧ hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2
  let S₂ := Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧ hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1
  let S₃ := Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧ hasEdge E t.2.2 t.1 ∧ hasEdge E t.1 t.2.1
  have hsub : Finset.univ.filter (fun t : V × V × V =>
      t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧
      ((hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2) ∨
       (hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1) ∨
       (hasEdge E t.2.2 t.1 ∧ hasEdge E t.1 t.2.1))) ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro t ht
    rw [Finset.mem_union, Finset.mem_union]
    have ht' := (Finset.mem_filter.mp ht).2
    rcases ht' with ⟨h1, h2, h3, hA | hB | hC⟩
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3, hA⟩))
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3, hB⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3, hC⟩)
  have hS3 : S₃.card = ∑ x : V, degE E x * (degE E x - 1) := by
    dsimp [S₃]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    let Nx := Finset.univ.filter fun y : V => hasEdge E x y
    have heq : (∑ y : V, ∑ z : V, if x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ hasEdge E z x ∧ hasEdge E x y then 1 else 0) =
        ∑ y ∈ Nx, (Nx.erase y).card := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hxy : hasEdge E x y
      · have hne_xy : x ≠ y := hxy.1
        have h2 : (Nx.erase y).card = ∑ z : V, if z ≠ y ∧ hasEdge E x z then 1 else 0 := by
          have : Nx.erase y = Finset.univ.filter fun z : V => z ≠ y ∧ hasEdge E x z := by
            ext z; simp [Nx]
          rw [this, Finset.card_eq_sum_ones, Finset.sum_filter]
        simp only [hxy, ↓reduceIte, h2]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hzx : hasEdge E x z
        · have hz_ne_x : z ≠ x := hzx.1.symm
          have hzx' : hasEdge E z x := hasEdge_symm.mpr hzx
          by_cases hzy : z = y
          · subst hzy; simp [hne_xy]
          · have hyz : y ≠ z := Ne.symm hzy
            simp [hne_xy, hyz, hz_ne_x, hzx, hzx', hzy]
        · have hnzx : ¬ hasEdge E z x := fun h => hzx (hasEdge_symm.mp h)
          simp [hzx, hnzx]
      · simp [hxy]
    rw [heq]
    have hcard_er : ∀ y ∈ Nx, (Nx.erase y).card = degE E x - 1 := fun y hy => by
      rw [Finset.card_erase_of_mem hy]; rfl
    rw [Finset.sum_congr rfl hcard_er, Finset.sum_const, smul_eq_mul]; rfl
  have hS1 : S₁.card = S₃.card := by
    let rot : (V × V × V) ≃ (V × V × V) :=
      { toFun := fun t => (t.2.1, t.2.2, t.1)
        invFun := fun t => (t.2.2, t.1, t.2.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    refine Finset.card_bij (fun t _ => rot t) ?_ (fun _ _ _ _ h => rot.injective h) ?_
    · intro ⟨a, b, c⟩ ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨h1, h2, h3, h4, h5⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h3, h1, h4, h5⟩
    · intro ⟨a, b, c⟩ ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨h1, h2, h3, h4, h5⟩
      exact ⟨(c, a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3, h1, h2, h4, h5⟩, rfl⟩
  have hS2 : S₂.card = S₃.card := by
    let rot2 : (V × V × V) ≃ (V × V × V) :=
      { toFun := fun t => (t.2.2, t.1, t.2.1)
        invFun := fun t => (t.2.1, t.2.2, t.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    refine Finset.card_bij (fun t _ => rot2 t) ?_ (fun _ _ _ _ h => rot2.injective h) ?_
    · intro ⟨a, b, c⟩ ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨h1, h2, h3, h4, h5⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3, h1, h2, h4, h5⟩
    · intro ⟨a, b, c⟩ ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨h1, h2, h3, h4, h5⟩
      exact ⟨(b, c, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h3, h1, h4, h5⟩, rfl⟩
  have hle := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (S₁ ∪ S₂) S₃
  have hu2 := Finset.card_union_le S₁ S₂
  unfold ordHappyTriples
  omega

private lemma ordHappyTriples_le_three_k_mul (E : Finset (Sym2 V)) :
    ordHappyTriples E ≤ 3 * (E.card * (E.card - 1)) := by
  let Tset := Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧
    ((hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2) ∨
     (hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1) ∨
     (hasEdge E t.2.2 t.1 ∧ hasEdge E t.1 t.2.1))
  let Pdiff : Finset (Sym2 V × Sym2 V) := (E ×ˢ E).filter fun p => p.1 ≠ p.2
  have hPdiff_card : Pdiff.card = E.card * (E.card - 1) := card_pair_diff E
  let f : V × V × V → Fin 3 × Sym2 V × Sym2 V := fun t =>
    if hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2 then (0, s(t.1, t.2.1), s(t.2.1, t.2.2))
    else if hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1 then (1, s(t.2.1, t.2.2), s(t.2.2, t.1))
    else (2, s(t.2.2, t.1), s(t.1, t.2.1))
  have h_rec : ∀ {a b c a' b' c' : V},
      a ≠ b → b ≠ c → c ≠ a → a' ≠ b' → b' ≠ c' → c' ≠ a' →
      s(a, b) = s(a', b') → s(b, c) = s(b', c') → a = a' ∧ b = b' ∧ c = c' := by
    intro a b c a' b' c' hab hbc hca hab' hbc' hca' h1 h2
    rw [Sym2.eq_iff] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact ⟨rfl, rfl, hc⟩
    · exact (hbc hc.symm).elim
    · exact (hab' hb).elim
    · exact (hca' hb.symm).elim
  have hcard_le : Tset.card ≤ (Finset.univ ×ˢ Pdiff : Finset (Fin 3 × Sym2 V × Sym2 V)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro ⟨a, b, c⟩ ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨hab, hbc, hca, hcases⟩
      dsimp only [f]
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ?_⟩
      split_ifs with h1 h2
      · exact ⟨Finset.mem_product.mpr ⟨h1.1.2, h1.2.2⟩, fun heq => by
          rw [Sym2.eq_iff] at heq; rcases heq with ⟨rfl, _⟩ | ⟨h, _⟩
          · exact hab rfl
          · exact hca h.symm⟩
      · exact ⟨Finset.mem_product.mpr ⟨h2.1.2, h2.2.2⟩, fun heq => by
          rw [Sym2.eq_iff] at heq; rcases heq with ⟨rfl, _⟩ | ⟨h, _⟩
          · exact hbc rfl
          · exact hab h.symm⟩
      · have h3 : hasEdge E c a ∧ hasEdge E a b := by tauto
        exact ⟨Finset.mem_product.mpr ⟨h3.1.2, h3.2.2⟩, fun heq => by
          rw [Sym2.eq_iff] at heq; rcases heq with ⟨rfl, _⟩ | ⟨h, _⟩
          · exact hca rfl
          · exact hbc h.symm⟩
    · intro ⟨a, b, c⟩ ht₁ ⟨a', b', c'⟩ ht₂ heq
      rcases (Finset.mem_filter.mp ht₁).2 with ⟨hab, hbc, hca, _⟩
      rcases (Finset.mem_filter.mp ht₂).2 with ⟨hab', hbc', hca', _⟩
      dsimp only [f] at heq
      split_ifs at heq with h1 h1' h2' h2 h2'' h2'''
      all_goals try (exfalso; have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide))
      · have h_e1 : s(a, b) = s(a', b') := congrArg (fun p => p.2.1) heq
        have h_e2 : s(b, c) = s(b', c') := congrArg (fun p => p.2.2) heq
        rcases h_rec hab hbc hca hab' hbc' hca' h_e1 h_e2 with ⟨rfl, rfl, rfl⟩; rfl
      · have h_e1 : s(b, c) = s(b', c') := congrArg (fun p => p.2.1) heq
        have h_e2 : s(c, a) = s(c', a') := congrArg (fun p => p.2.2) heq
        rcases h_rec hbc hca hab hbc' hca' hab' h_e1 h_e2 with ⟨rfl, rfl, rfl⟩; rfl
      · have h_e1 : s(c, a) = s(c', a') := congrArg (fun p => p.2.1) heq
        have h_e2 : s(a, b) = s(a', b') := congrArg (fun p => p.2.2) heq
        rcases h_rec hca hab hbc hca' hab' hbc' h_e1 h_e2 with ⟨rfl, rfl, rfl⟩; rfl
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hPdiff_card] at hcard_le
  exact hcard_le

/-- Pure arithmetic convexity lemma for `f_k(d) = d(d-1) + (k-d+1)(k-d)`. -/
private lemma happy_conv_nat {k d l : ℕ} (hd_le_k : d ≤ k) (hv_ge : k ≤ 2 * d) (hv_le : d ≤ l) :
    d * (d - 1) + 2 * (k - d) + (k - d) * (k - d - 1) ≤ l * (l - 1) + (k - l + 1) * (k - l) := by
  by_cases hlk : l ≤ k
  · have hnat1 : ((d * (d - 1) + 2 * (k - d) + (k - d) * (k - d - 1) : ℕ) : ℤ) =
        (d : ℤ) * ((d : ℤ) - 1) + ((k : ℤ) - d + 1) * ((k : ℤ) - d) := by
      have hd1 : d = 0 ∨ 1 ≤ d := by omega
      have hkd : k - d = 0 ∨ 1 ≤ k - d := by omega
      rcases hd1 with rfl | hd1
      · have : k = 0 := by omega
        subst this; simp
      · rcases hkd with hkd0 | hkd1
        · have : d = k := by omega
          subst this; simp [Nat.cast_sub hd1]
        · push_cast [Nat.cast_sub hd1, Nat.cast_sub hd_le_k, Nat.cast_sub hkd1]; ring
    have hnat2 : ((l * (l - 1) + (k - l + 1) * (k - l) : ℕ) : ℤ) =
        (l : ℤ) * ((l : ℤ) - 1) + ((k : ℤ) - l + 1) * ((k : ℤ) - l) := by
      have hl1 : l = 0 ∨ 1 ≤ l := by omega
      rcases hl1 with rfl | hl1
      · have : k = 0 := by omega
        subst this; simp
      · push_cast [Nat.cast_sub hl1, Nat.cast_sub hlk]; ring
    have hle_z : ((d * (d - 1) + 2 * (k - d) + (k - d) * (k - d - 1) : ℕ) : ℤ) ≤
        ((l * (l - 1) + (k - l + 1) * (k - l) : ℕ) : ℤ) := by
      rw [hnat1, hnat2]
      by_cases heq : d = l
      · subst heq; exact le_rfl
      · have h1 : (d : ℤ) + 1 ≤ (l : ℤ) := by omega
        have h2 : (k : ℤ) ≤ 2 * (d : ℤ) := by exact_mod_cast hv_ge
        nlinarith
    exact_mod_cast hle_z
  · have h1 : d * (d - 1) + 2 * (k - d) + (k - d) * (k - d - 1) ≤ k * (k - 1) := by
      have hd1 : d = 0 ∨ 1 ≤ d := by omega
      have hkd : k - d = 0 ∨ 1 ≤ k - d := by omega
      rcases hd1 with rfl | hd1
      · have : k = 0 := by omega
        subst this; simp
      · rcases hkd with hkd0 | hkd1
        · have : d = k := by omega
          subst this; simp
        · have hk1 : 1 ≤ k := by omega
          have hz : ((d * (d - 1) + 2 * (k - d) + (k - d) * (k - d - 1) : ℕ) : ℤ) ≤
              ((k * (k - 1) : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub hd1, Nat.cast_sub hd_le_k, Nat.cast_sub hkd1, Nat.cast_sub hk1]
            have h2 : (k : ℤ) ≤ 2 * (d : ℤ) := by exact_mod_cast hv_ge
            have h3 : (d : ℤ) ≤ (k : ℤ) := by exact_mod_cast hd_le_k
            nlinarith
          exact_mod_cast hz
    have h2 : k * (k - 1) ≤ l * (l - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- Case A of Happy-Triple Lemma (3 lines, Hompe–Qu–Spirkl Claim 1):
If `∃ v` with `k ≤ 2 * degE E v` and `degE E v ≤ l`, then
`ordHappyTriples E ≤ 3 * (l * (l - 1) + (k - l + 1) * (k - l))`. -/
private lemma ordHappyTriples_of_large_deg (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    {l : ℕ} {v : V} (hv_ge : E.card ≤ 2 * degE E v) (hv_le : degE E v ≤ l) :
    ordHappyTriples E ≤ 3 * (l * (l - 1) + (E.card - l + 1) * (E.card - l)) := by
  let d := degE E v
  let k := E.card
  let Ev := E.filter fun e => v ∈ e
  let E' := E \ Ev
  have hEv_card : Ev.card = d := card_incident_edges E hloop v
  have hE'_card : E'.card = k - d := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hEv_card]
  have hd_le_k : d ≤ k := by rw [← hEv_card]; exact Finset.card_le_card (Finset.filter_subset _ _)
  let Tset := Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧
    ((hasEdge E t.1 t.2.1 ∧ hasEdge E t.2.1 t.2.2) ∨
     (hasEdge E t.2.1 t.2.2 ∧ hasEdge E t.2.2 t.1) ∨
     (hasEdge E t.2.2 t.1 ∧ hasEdge E t.1 t.2.1))
  let T1 := Tset.filter fun t =>
    (t.1 = v ∧ hasEdge E v t.2.1 ∧ hasEdge E v t.2.2) ∨
    (t.2.1 = v ∧ hasEdge E v t.1 ∧ hasEdge E v t.2.2) ∨
    (t.2.2 = v ∧ hasEdge E v t.1 ∧ hasEdge E v t.2.1)
  let T2 := Tset.filter fun t =>
    (t.1 = v ∧ hasEdge E' t.2.1 t.2.2) ∨
    (t.2.1 = v ∧ hasEdge E' t.1 t.2.2) ∨
    (t.2.2 = v ∧ hasEdge E' t.1 t.2.1)
  let T3 := Finset.univ.filter fun t : V × V × V =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 ∧
    ((hasEdge E' t.1 t.2.1 ∧ hasEdge E' t.2.1 t.2.2) ∨
     (hasEdge E' t.2.1 t.2.2 ∧ hasEdge E' t.2.2 t.1) ∨
     (hasEdge E' t.2.2 t.1 ∧ hasEdge E' t.1 t.2.1))
  have hcov : Tset ⊆ T1 ∪ T2 ∪ T3 := by
    intro ⟨a, b, c⟩ ht
    rw [Finset.mem_union, Finset.mem_union]
    rcases (Finset.mem_filter.mp ht).2 with ⟨hab, hbc, hca, hE⟩
    have hE' : ∀ x y, x ≠ v → y ≠ v → hasEdge E x y → hasEdge E' x y := fun x y hxv hyv hxy => by
      refine ⟨hxy.1, Finset.mem_sdiff.mpr ⟨hxy.2, fun hv => ?_⟩⟩
      rcases Sym2.mem_iff.mp (Finset.mem_filter.mp hv).2 with rfl | rfl
      · exact hxv rfl
      · exact hyv rfl
    by_cases hav : a = v
    · subst hav
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, Or.inl ⟨rfl, hE' b c hab.symm hca h2⟩⟩))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, Or.inl ⟨rfl, hE' b c hab.symm hca h1⟩⟩))
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨ht, Or.inl ⟨rfl, h2, hasEdge_symm.mp h1⟩⟩))
    · by_cases hbv : b = v
      · subst hbv
        rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨ht, Or.inr (Or.inl ⟨rfl, hasEdge_symm.mp h1, h2⟩)⟩))
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, Or.inr (Or.inl ⟨rfl, hE' a c hab hbc.symm (hasEdge_symm.mp h2)⟩)⟩))
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, Or.inr (Or.inl ⟨rfl, hE' a c hab hbc.symm (hasEdge_symm.mp h1)⟩)⟩))
      · by_cases hcv : c = v
        · subst hcv
          rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, Or.inr (Or.inr ⟨rfl, hE' a b hca.symm hbc h1⟩)⟩))
          · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨ht, Or.inr (Or.inr ⟨rfl, h2, hasEdge_symm.mp h1⟩)⟩))
          · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨ht, Or.inr (Or.inr ⟨rfl, hE' a b hca.symm hbc h2⟩)⟩))
        · refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hbc, hca, ?_⟩)
          rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨hE' a b hav hbv h1, hE' b c hbv hcv h2⟩
          · exact Or.inr (Or.inl ⟨hE' b c hbv hcv h1, hE' c a hcv hav h2⟩)
          · exact Or.inr (Or.inr ⟨hE' c a hcv hav h1, hE' a b hav hbv h2⟩)
  -- Helper: bounding `T1` and `T2` via injection `(a, b, c) ↦ (pos ∈ Fin 3, other two)`!
  let Nv := Finset.univ.filter fun y : V => hasEdge E v y
  let NvDiff := (Nv ×ˢ Nv).filter fun p => p.1 ≠ p.2
  have hT1_le : T1.card ≤ 3 * (d * (d - 1)) := by
    let g1 : V × V × V → Fin 3 × V × V := fun t =>
      if t.1 = v then (0, t.2.1, t.2.2) else if t.2.1 = v then (1, t.1, t.2.2) else (2, t.1, t.2.1)
    have hle : T1.card ≤ (Finset.univ ×ˢ NvDiff : Finset (Fin 3 × V × V)).card := by
      refine Finset.card_le_card_of_injOn g1 ?_ ?_
      · intro ⟨a, b, c⟩ ht
        rcases Finset.mem_filter.mp ht with ⟨ht0, hcase⟩
        rcases (Finset.mem_filter.mp ht0).2 with ⟨hab, hbc, hca, _⟩
        dsimp only [g1]
        rcases hcase with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
        · simp only [↓reduceIte]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩, hbc⟩⟩
        · simp only [hab, ↓reduceIte]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩, hca.symm⟩⟩
        · simp only [hca.symm, hbc, ↓reduceIte]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩, hab⟩⟩
      · intro ⟨a, b, c⟩ ht₁ ⟨a', b', c'⟩ ht₂ heq
        rcases Finset.mem_filter.mp ht₁ with ⟨_, h1⟩
        rcases Finset.mem_filter.mp ht₂ with ⟨_, h2⟩
        dsimp only [g1] at heq
        by_cases ha1 : a = v <;> by_cases ha2 : a' = v
        · subst ha1; subst ha2; simp only [↓reduceIte, Prod.mk.injEq] at heq
          rcases heq with ⟨_, rfl, rfl⟩; rfl
        · by_cases hb2 : b' = v
          · simp only [ha1, ha2, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · simp only [ha1, ha2, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
        · by_cases hb1 : b = v
          · simp only [ha1, ha2, hb1, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · simp only [ha1, ha2, hb1, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
        · by_cases hb1 : b = v <;> by_cases hb2 : b' = v
          · subst hb1; subst hb2; simp only [ha1, ha2, ↓reduceIte, Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl, rfl⟩; rfl
          · simp only [ha1, ha2, hb1, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · simp only [ha1, ha2, hb1, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · have hc1 : c = v := by rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> tauto
            have hc2 : c' = v := by rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> tauto
            subst hc1; subst hc2; simp only [ha1, ha2, hb1, hb2, ↓reduceIte, Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl, rfl⟩; rfl
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, card_pair_diff Nv] at hle
    exact hle
  let OrdE' := Finset.univ.filter fun p : V × V => hasEdge E' p.1 p.2
  have hOrdE'_card : OrdE'.card = 2 * E'.card := by
    have hloop' : ∀ e ∈ E', ¬ e.IsDiag := fun e he => hloop e (Finset.mem_sdiff.mp he).1
    rw [← sym2_card_double E' hloop']
    simp only [OrdE', degE, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  have hT2_le : T2.card ≤ 6 * (k - d) := by
    let g2 : V × V × V → Fin 3 × V × V := fun t =>
      if t.1 = v then (0, t.2.1, t.2.2) else if t.2.1 = v then (1, t.1, t.2.2) else (2, t.1, t.2.1)
    have hle : T2.card ≤ (Finset.univ ×ˢ OrdE' : Finset (Fin 3 × V × V)).card := by
      refine Finset.card_le_card_of_injOn g2 ?_ ?_
      · intro ⟨a, b, c⟩ ht
        rcases Finset.mem_filter.mp ht with ⟨ht0, hcase⟩
        rcases (Finset.mem_filter.mp ht0).2 with ⟨hab, hbc, hca, _⟩
        dsimp only [g2]
        rcases hcase with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩
        · simp only [↓reduceIte]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
        · simp only [hab, ↓reduceIte]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
        · simp only [hca.symm, hbc, ↓reduceIte]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
      · intro ⟨a, b, c⟩ ht₁ ⟨a', b', c'⟩ ht₂ heq
        rcases Finset.mem_filter.mp ht₁ with ⟨_, h1⟩
        rcases Finset.mem_filter.mp ht₂ with ⟨_, h2⟩
        dsimp only [g2] at heq
        by_cases ha1 : a = v <;> by_cases ha2 : a' = v
        · subst ha1; subst ha2; simp only [↓reduceIte, Prod.mk.injEq] at heq
          rcases heq with ⟨_, rfl, rfl⟩; rfl
        · by_cases hb2 : b' = v
          · simp only [ha1, ha2, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · simp only [ha1, ha2, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
        · by_cases hb1 : b = v
          · simp only [ha1, ha2, hb1, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · simp only [ha1, ha2, hb1, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
        · by_cases hb1 : b = v <;> by_cases hb2 : b' = v
          · subst hb1; subst hb2; simp only [ha1, ha2, ↓reduceIte, Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl, rfl⟩; rfl
          · simp only [ha1, ha2, hb1, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · simp only [ha1, ha2, hb1, hb2, ↓reduceIte] at heq
            have h0 := congrArg Prod.fst heq; dsimp only at h0; exact absurd h0 (by decide)
          · have hc1 : c = v := by rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> tauto
            have hc2 : c' = v := by rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> tauto
            subst hc1; subst hc2; simp only [ha1, ha2, hb1, hb2, ↓reduceIte, Prod.mk.injEq] at heq
            rcases heq with ⟨_, rfl, rfl⟩; rfl
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hOrdE'_card, hE'_card] at hle
    omega
  have hT3_le : T3.card ≤ 3 * ((k - d) * (k - d - 1)) := by
    have h := ordHappyTriples_le_three_k_mul E'
    rw [hE'_card] at h; exact h
  have htot : ordHappyTriples E ≤ 3 * (d * (d - 1)) + 6 * (k - d) + 3 * ((k - d) * (k - d - 1)) := by
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le (T1 ∪ T2) T3
    have h3 := Finset.card_union_le T1 T2
    change Tset.card ≤ _; omega
  have hconv := happy_conv_nat hd_le_k hv_ge hv_le
  change ordHappyTriples E ≤ 3 * (l * (l - 1) + (k - l + 1) * (k - l))
  omega

/-- Pure arithmetic lemma for Subcase `k ≥ 15` of the Zero-DP Happy-Triple Lemma. -/
private lemma zero_dp_arith {k : ℕ} (hk15 : 15 ≤ k) :
    let D := (k - 1) / 2
    let s := k / 3
    let l := (929 * k) / 1000
    (D - 1) * (k + 6) + (s - 1) * (k - 6) ≤ l * (l - 1) + (k - l + 1) * (k - l) := by
  intro D s l
  by_cases hk21 : k ≤ 21
  · dsimp only [D, s, l]
    interval_cases k <;> norm_num
  · have hk22 : 22 ≤ k := by omega
    have hl_ge_1 : 1 ≤ l := by dsimp [l]; omega
    have hl_le_k : l ≤ k := by dsimp [l]; omega
    have hD1 : 1 ≤ D := by dsimp [D]; omega
    have hs1 : 1 ≤ s := by dsimp [s]; omega
    have hD_le : 2 * (D : ℝ) ≤ (k : ℝ) - 1 := by
      have : 2 * D ≤ k - 1 := by dsimp [D]; omega
      have h1 : ((2 * D : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 1 ≤ k)] at h1; push_cast at h1; linarith
    have hs_le : 3 * (s : ℝ) ≤ (k : ℝ) := by
      have : 3 * s ≤ k := by dsimp [s]; omega
      have h1 : ((3 * s : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
      push_cast at h1; linarith
    have hl_lb : (929 * (k : ℝ) - 999) / 1000 ≤ (l : ℝ) := by
      have : 929 * k - 999 ≤ 1000 * l := by dsimp [l]; omega
      have h1 : ((929 * k - 999 : ℕ) : ℝ) ≤ ((1000 * l : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 999 ≤ 929 * k)] at h1; push_cast at h1; linarith
    have hl_ub : (l : ℝ) ≤ (929 * (k : ℝ)) / 1000 := by
      have : 1000 * l ≤ 929 * k := by dsimp [l]; omega
      have h1 : ((1000 * l : ℕ) : ℝ) ≤ ((929 * k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h1; linarith
    have hreal : (((D - 1) * (k + 6) + (s - 1) * (k - 6) : ℕ) : ℝ) ≤
        ((l * (l - 1) + (k - l + 1) * (k - l) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hD1, Nat.cast_sub hs1, Nat.cast_sub (by omega : 6 ≤ k),
        Nat.cast_sub hl_ge_1, Nat.cast_sub hl_le_k]
      have hk_r : (22 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk22
      nlinarith [sq_nonneg ((l : ℝ) - (929 * (k : ℝ) - 999) / 1000)]
    exact_mod_cast hreal

/-- **6-Line ZERO-DP Elementary Happy-Triple Lemma (All `k ≥ 1`, `l = ⌊929·k/1000⌋`)**:
Completely eliminates Hompe–Qu–Spirkl's 5-page `Lemma 2` + `k ≤ 103` computer DP! -/
private lemma ordHappyTriples_le_zero_dp (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hmax : ∀ x : V, degE E x ≤ (929 * E.card) / 1000) :
    let l := (929 * E.card) / 1000
    ordHappyTriples E ≤ 3 * (l * (l - 1) + (E.card - l + 1) * (E.card - l)) := by
  intro l
  let k := E.card
  by_cases hex : ∃ v : V, k ≤ 2 * degE E v
  · obtain ⟨v, hv⟩ := hex
    exact ordHappyTriples_of_large_deg E hloop hv (hmax v)
  · push Not at hex
    let D := (k - 1) / 2
    have hdeg_le_D : ∀ x : V, degE E x ≤ D := fun x => by have := hex x; omega
    have hsum_deg : ∑ x : V, degE E x = 2 * k := sym2_card_double E hloop
    have htri := ordHappyTriples_le_three_sum_deg_mul E
    suffices hdeg_sum : ∑ x : V, degE E x * (degE E x - 1) ≤ l * (l - 1) + (k - l + 1) * (k - l) by
      change ordHappyTriples E ≤ 3 * (l * (l - 1) + (k - l + 1) * (k - l))
      omega
    by_cases hk14 : k ≤ 14
    · have h1 : ∑ x : V, degE E x * (degE E x - 1) ≤ (D - 1) * (2 * k) := by
        rw [← hsum_deg, Finset.mul_sum]
        refine Finset.sum_le_sum fun x _ => ?_
        rw [mul_comm]
        exact Nat.mul_le_mul_right (degE E x) (Nat.sub_le_sub_right (hdeg_le_D x) 1)
      have h2 : (D - 1) * (2 * k) ≤ l * (l - 1) + (k - l + 1) * (k - l) := by
        change ((k - 1) / 2 - 1) * (2 * k) ≤ (929 * k / 1000) * (929 * k / 1000 - 1) +
          (k - 929 * k / 1000 + 1) * (k - 929 * k / 1000)
        interval_cases k <;> norm_num
      exact le_trans h1 h2
    · have hk15 : 15 ≤ k := by omega
      let s := k / 3
      let H := Finset.univ.filter fun x : V => s < degE E x
      let L := Finset.univ.filter fun x : V => ¬ (s < degE E x)
      let SH := ∑ x ∈ H, degE E x
      have hSH_ub : 2 * SH ≤ 2 * k + H.card * (H.card - 1) := by
        let E_in := E.filter fun e => ∀ x ∈ e, x ∈ H
        have hEin_le : 2 * E_in.card ≤ H.card * (H.card - 1) := by
          have hloop_in : ∀ e ∈ E_in, ¬ e.IsDiag := fun e he => hloop e (Finset.mem_filter.mp he).1
          rw [← sym2_card_double E_in hloop_in]
          have hdeg_in : ∀ x : V, degE E_in x ≤ if x ∈ H then H.card - 1 else 0 := by
            intro x
            by_cases hx : x ∈ H
            · simp only [hx, ↓reduceIte]
              have hsub : Finset.univ.filter (fun y => hasEdge E_in x y) ⊆ H.erase x := by
                intro y hy
                have hxy := (Finset.mem_filter.mp hy).2
                have hyH : y ∈ H := (Finset.mem_filter.mp hxy.2).2 y (Sym2.mem_mk_right x y)
                exact Finset.mem_erase.mpr ⟨hxy.1.symm, hyH⟩
              calc degE E_in x ≤ (H.erase x).card := Finset.card_le_card hsub
                _ = H.card - 1 := Finset.card_erase_of_mem hx
            · simp only [hx, ↓reduceIte, Nat.le_zero]
              rw [degE, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro y _ hxy
              exact hx ((Finset.mem_filter.mp hxy.2).2 x (Sym2.mem_mk_left x y))
          calc ∑ x : V, degE E_in x
              ≤ ∑ x : V, (if x ∈ H then H.card - 1 else 0) := Finset.sum_le_sum fun x _ => hdeg_in x
            _ = H.card * (H.card - 1) := by
                rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
                congr 2; ext x; simp
        have hSH_eq : SH ≤ E.card + E_in.card := by
          have hcount : SH = ∑ e ∈ E, (H.filter fun x => x ∈ e).card := by
            dsimp [SH]
            have hdeg_e : ∀ x : V, degE E x = (E.filter fun e => x ∈ e).card :=
              fun x => (card_incident_edges E hloop x).symm
            simp_rw [hdeg_e, Finset.card_eq_sum_ones, Finset.sum_filter]
            exact Finset.sum_comm
          rw [hcount]
          have hpt : ∀ e ∈ E, (H.filter fun x => x ∈ e).card ≤ 1 + if e ∈ E_in then 1 else 0 := by
            intro e he
            induction e using Sym2.ind with
            | _ a b =>
              have hsub2 : H.filter (fun x => x ∈ s(a, b)) ⊆ {a, b} := by
                intro x hx
                rcases Sym2.mem_iff.mp (Finset.mem_filter.mp hx).2 with rfl | rfl <;> simp
              by_cases hin : s(a, b) ∈ E_in
              · simp only [hin, ↓reduceIte]
                exact le_trans (Finset.card_le_card hsub2) Finset.card_le_two
              · simp only [hin, ↓reduceIte, add_zero]
                have hnot : ¬ (a ∈ H ∧ b ∈ H) := fun ⟨ha, hb⟩ => hin (Finset.mem_filter.mpr ⟨he, fun x hx => by
                  rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩)
                by_cases ha : a ∈ H
                · have hb : b ∉ H := fun hb => hnot ⟨ha, hb⟩
                  have hsub1 : H.filter (fun x => x ∈ s(a, b)) ⊆ {a} := by
                    intro x hx
                    rcases Finset.mem_filter.mp hx with ⟨hxH, hxs⟩
                    rcases Sym2.mem_iff.mp hxs with rfl | rfl
                    · simp
                    · exact (hb hxH).elim
                  exact le_trans (Finset.card_le_card hsub1) (by simp)
                · have hsub1 : H.filter (fun x => x ∈ s(a, b)) ⊆ {b} := by
                    intro x hx
                    rcases Finset.mem_filter.mp hx with ⟨hxH, hxs⟩
                    rcases Sym2.mem_iff.mp hxs with rfl | rfl
                    · exact (ha hxH).elim
                    · simp
                  exact le_trans (Finset.card_le_card hsub1) (by simp)
          calc ∑ e ∈ E, (H.filter fun x => x ∈ e).card
              ≤ ∑ e ∈ E, (1 + if e ∈ E_in then 1 else 0) := Finset.sum_le_sum hpt
            _ = E.card + E_in.card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.sum_filter,
                  Finset.sum_const, smul_eq_mul, mul_one]
                congr 2; ext e; simp [E_in]
        omega
      have hSH_lb : H.card * (s + 1) ≤ SH := by
        calc H.card * (s + 1) = ∑ _x ∈ H, (s + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ x ∈ H, degE E x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      have hSH_le_2k : SH ≤ 2 * k := by
        rw [← hsum_deg]; exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      have hH_le4 : H.card ≤ 4 := by
        have hH5 : H.card ≤ 5 := by
          have : H.card * (s + 1) ≤ 2 * k := le_trans hSH_lb hSH_le_2k
          have hs3 : k < 3 * (s + 1) := by dsimp [s]; omega
          nlinarith
        by_contra hgt4
        have hEq5 : H.card = 5 := by omega
        rw [hEq5] at hSH_lb hSH_ub
        dsimp [s] at hSH_lb
        omega
      have hSH_le_k6 : SH ≤ k + 6 := by
        have h4 : H.card * (H.card - 1) ≤ 12 := by
          have : H.card ≤ 4 := hH_le4
          interval_cases H.card <;> norm_num
        omega
      have hHL_disj : Disjoint H L := by
        rw [Finset.disjoint_left]; intro x h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hHL_union : H ∪ L = Finset.univ := by
        ext x; simp only [H, L, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : s < degE E x <;> simp [h]
      have hsum_L : ∑ x ∈ L, degE E x = 2 * k - SH := by
        have hu := Finset.sum_union hHL_disj (f := fun x => degE E x)
        rw [hHL_union, hsum_deg] at hu; omega
      have hbound_nat : ∑ x : V, degE E x * (degE E x - 1) ≤
          (D - 1) * SH + (s - 1) * (2 * k - SH) := by
        rw [← hHL_union, Finset.sum_union hHL_disj]
        refine Nat.add_le_add ?_ ?_
        · rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          rw [mul_comm]; exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (hdeg_le_D x) 1)
        · rw [← hsum_L, Finset.mul_sum]
          refine Finset.sum_le_sum fun x hx => ?_
          have hxL : degE E x ≤ s := Nat.le_of_not_lt (Finset.mem_filter.mp hx).2
          rw [mul_comm]; exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hxL 1)
      have hs_le_D : s ≤ D := by dsimp [s, D]; omega
      have hstep_k6 : (D - 1) * SH + (s - 1) * (2 * k - SH) ≤
          (D - 1) * (k + 6) + (s - 1) * (k - 6) := by
        have hcast : ((D - 1 : ℕ) : ℤ) * (SH : ℤ) + ((s - 1 : ℕ) : ℤ) * ((2 * k - SH : ℕ) : ℤ) ≤
            ((D - 1 : ℕ) : ℤ) * ((k + 6 : ℕ) : ℤ) + ((s - 1 : ℕ) : ℤ) * ((k - 6 : ℕ) : ℤ) := by
          have h1z : ((s - 1 : ℕ) : ℤ) ≤ ((D - 1 : ℕ) : ℤ) := by
            exact_mod_cast Nat.sub_le_sub_right hs_le_D 1
          have hSHz : (SH : ℤ) ≤ (k : ℤ) + 6 := by exact_mod_cast hSH_le_k6
          rw [Nat.cast_sub hSH_le_2k, Nat.cast_sub (by omega : 6 ≤ k)]
          push_cast; nlinarith
        exact_mod_cast hcast
      exact le_trans (le_trans hbound_nat hstep_k6) (zero_dp_arith hk15)

end GraphCounting

/-! ## Section 3: Modular Hompe–Qu–Spirkl Section-4 Lemmas & Main Theorem -/

section HompeQuSpirkl
open Classical

variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
variable {C : Type v} [Fintype C] [DecidableEq C]

omit [Fintype C] in
/-- Step 1 (`Claim delta`): strictly more than `(1 - δ) · n` trimmed color classes are concentrated. -/
private lemma rainbow_claim_conc_gt
    {t δ : ℝ} (hδ_pos : 0 < δ)
    (h3 : (1 - δ * (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * t < (8 / 3 : ℝ) * (t - 1 / 4))
    (C₀ : Finset C) (hC₀_card : C₀.card = Fintype.card V)
    (k : ℕ) (hk_ge3 : 3 ≤ k) (hk_ge : t * (Fintype.card V : ℝ) ≤ (k : ℝ))
    (Ec : {c : C // c ∈ C₀} → Finset (Sym2 V))
    (hEc_card : ∀ c, (Ec c).card = k)
    (hEc_loop : ∀ c, ∀ e ∈ Ec c, ¬ e.IsDiag)
    (E : Finset (Sym2 V)) (hE_card : E.card = Fintype.card V * k)
    (hE_loop : ∀ e ∈ E, ¬ e.IsDiag)
    (htri_le : ordTriangles E ≤ ∑ c ∈ C₀.attach, ordHappyTriples (Ec c)) :
    (1 - δ) * (Fintype.card V : ℝ) <
      ((C₀.attach.filter fun c => ∃ v : V, (929 / 1000 : ℝ) * (k : ℝ) ≤ (degE (Ec c) v : ℝ)).card : ℝ) := by
  let n := Fintype.card V
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hk_pos : 1 ≤ k := by omega
  let t₁ : ℝ := (k : ℝ) / (n : ℝ)
  have ht_le_t1 : t ≤ t₁ := by dsimp [t₁]; rw [le_div_iff₀ hn_r]; exact hk_ge
  let isConc : {c : C // c ∈ C₀} → Prop := fun c => ∃ v : V, (929 / 1000 : ℝ) * (k : ℝ) ≤ (degE (Ec c) v : ℝ)
  let Conc := C₀.attach.filter isConc
  let NonConc := C₀.attach.filter fun c => ¬ isConc c
  change (1 - δ) * (n : ℝ) < (Conc.card : ℝ)
  by_contra hle_conc
  push Not at hle_conc
  have hdisj : Disjoint Conc NonConc := by
    rw [Finset.disjoint_left]; intro c h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion : Conc ∪ NonConc = C₀.attach := by
    ext c; simp only [Conc, NonConc, Finset.mem_union, Finset.mem_filter, Finset.mem_attach, true_and]
    by_cases h : isConc c <;> simp [h]
  have hcard_sum : (Conc.card : ℝ) + (NonConc.card : ℝ) = (n : ℝ) := by
    have hnat := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_attach, hC₀_card] at hnat
    have hcast : ((Conc.card + NonConc.card : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hnat.symm
    push_cast at hcast; exact hcast
  have hNonConc_ge : δ * (n : ℝ) ≤ (NonConc.card : ℝ) := by linarith
  have hConc_ht : ∀ c ∈ Conc, (ordHappyTriples (Ec c) : ℝ) ≤ 3 * (k : ℝ) ^ 2 := by
    intro c _
    have h := ordHappyTriples_le_three_k_mul (Ec c)
    rw [hEc_card c] at h
    have h1 : (ordHappyTriples (Ec c) : ℝ) ≤ ((3 * (k * (k - 1)) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hk_pos] at h1; nlinarith
  have hNonConc_ht : ∀ c ∈ NonConc,
      (ordHappyTriples (Ec c) : ℝ) ≤
        3 * (1 - (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * (k : ℝ) ^ 2 := by
    intro c hc
    have hnc : ¬ isConc c := (Finset.mem_filter.mp hc).2
    have hmax : ∀ x : V, degE (Ec c) x ≤ (929 * (Ec c).card) / 1000 := by
      intro x
      have hlt : (degE (Ec c) x : ℝ) < (929 / 1000 : ℝ) * (k : ℝ) := by
        by_contra hge; push Not at hge; exact hnc ⟨x, hge⟩
      rw [hEc_card c]
      have hnat : 1000 * degE (Ec c) x < 929 * k := by
        have : ((1000 * degE (Ec c) x : ℕ) : ℝ) < ((929 * k : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      omega
    have hdp := ordHappyTriples_le_zero_dp (Ec c) (hEc_loop c) hmax
    rw [hEc_card c] at hdp
    let l := (929 * k) / 1000
    have hl_ge_half : k + 1 ≤ 2 * l := by dsimp [l]; omega
    have hl_le_k : l ≤ k := by dsimp [l]; omega
    have hl1 : 1 ≤ l := by omega
    have hl_le_r : (l : ℝ) ≤ (929 / 1000 : ℝ) * (k : ℝ) := by
      have : 1000 * l ≤ 929 * k := by dsimp [l]; omega
      have h1 : ((1000 * l : ℕ) : ℝ) ≤ ((929 * k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h1; linarith
    have hdp_r : (ordHappyTriples (Ec c) : ℝ) ≤
        3 * ((l : ℝ) * ((l : ℝ) - 1) + ((k : ℝ) - (l : ℝ) + 1) * ((k : ℝ) - (l : ℝ))) := by
      have h1 : (ordHappyTriples (Ec c) : ℝ) ≤
          ((3 * (l * (l - 1) + (k - l + 1) * (k - l)) : ℕ) : ℝ) := by exact_mod_cast hdp
      push_cast [Nat.cast_sub hl1, Nat.cast_sub hl_le_k] at h1; linarith
    have hge_r : (k : ℝ) + 1 ≤ 2 * (l : ℝ) := by
      have h1 : ((k + 1 : ℕ) : ℝ) ≤ ((2 * l : ℕ) : ℝ) := by exact_mod_cast hl_ge_half
      push_cast at h1; linarith
    have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    have hconv_r : (l : ℝ) * ((l : ℝ) - 1) + ((k : ℝ) - (l : ℝ) + 1) * ((k : ℝ) - (l : ℝ)) ≤
        (1 - (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * (k : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ (929 / 1000 : ℝ) * (k : ℝ) - (l : ℝ) by linarith)
        (show 0 ≤ 2 * (l : ℝ) + 2 * ((929 / 1000 : ℝ) * (k : ℝ)) - 2 * (k : ℝ) - 2 by linarith)]
    linarith
  have htri_ub : (ordTriangles E : ℝ) ≤
      3 * (n : ℝ) * (1 - δ * (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * (k : ℝ) ^ 2 := by
    have hsum_r : (ordTriangles E : ℝ) ≤ ∑ c ∈ C₀.attach, (ordHappyTriples (Ec c) : ℝ) := by
      have h1 : (ordTriangles E : ℝ) ≤ ((∑ c ∈ C₀.attach, ordHappyTriples (Ec c) : ℕ) : ℝ) := by
        exact_mod_cast htri_le
      simpa [Nat.cast_sum] using h1
    rw [← hunion, Finset.sum_union hdisj] at hsum_r
    have h1 : ∑ c ∈ Conc, (ordHappyTriples (Ec c) : ℝ) ≤ (Conc.card : ℝ) * (3 * (k : ℝ) ^ 2) := by
      calc ∑ c ∈ Conc, (ordHappyTriples (Ec c) : ℝ)
          ≤ ∑ _c ∈ Conc, (3 * (k : ℝ) ^ 2) := Finset.sum_le_sum hConc_ht
        _ = (Conc.card : ℝ) * (3 * (k : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ c ∈ NonConc, (ordHappyTriples (Ec c) : ℝ) ≤
        (NonConc.card : ℝ) * (3 * (1 - (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * (k : ℝ) ^ 2) := by
      calc ∑ c ∈ NonConc, (ordHappyTriples (Ec c) : ℝ)
          ≤ ∑ _c ∈ NonConc, _ := Finset.sum_le_sum hNonConc_ht
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    nlinarith [show (0 : ℝ) ≤ 3 * (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2) * (k : ℝ) ^ 2 by positivity]
  have hgood := goodman_ordTriangles E hE_loop
  rw [hE_card] at hgood; push_cast at hgood
  have hk_eq : (k : ℝ) = t₁ * (n : ℝ) := by dsimp [t₁]; exact (div_mul_cancel₀ _ hn_r.ne').symm
  rw [hk_eq] at hgood htri_ub
  have ht1_pos : 0 < t₁ := by dsimp [t₁]; positivity
  have hfac_pos : 0 < 3 * t₁ * (n : ℝ) ^ 4 := by positivity
  have hcontra : (8 / 3 : ℝ) * (t₁ - 1 / 4) ≤
      (1 - δ * (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * t₁ := by
    by_contra hgt; push Not at hgt
    have hmul : (3 * t₁ * (n : ℝ) ^ 4) * ((1 - δ * (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * t₁) <
        (3 * t₁ * (n : ℝ) ^ 4) * ((8 / 3 : ℝ) * (t₁ - 1 / 4)) :=
      mul_lt_mul_of_pos_left hgt hfac_pos
    nlinarith
  nlinarith

omit [Fintype C] in
/-- Step 2 (Case 1): Two distinct concentrated color classes sharing a center `v` contradict `h2`. -/
private lemma rainbow_case_shared_center
    {t : ℝ} (ht_pos : 0 < t) (h2 : 1 / 2 - (929 / 1000 : ℝ) ^ 2 * t ^ 2 < t)
    (G : EdgeColoredGraph V C) (hno_rb : ¬ G.HasRainbowTriangle)
    (C₀ : Finset C) (k : ℕ) (hk_ge : t * (Fintype.card V : ℝ) ≤ (k : ℝ))
    (h2k_le : 2 * k ≤ Fintype.card V - 1)
    (Ec : {c : C // c ∈ C₀} → Finset (Sym2 V))
    (hEc_sub : ∀ c, Ec c ⊆ G.colorEdges c.1)
    (hEc_card : ∀ c, (Ec c).card = k)
    (hEc_loop : ∀ c, ∀ e ∈ Ec c, ¬ e.IsDiag)
    (E : Finset (Sym2 V)) (hE_def : E = C₀.attach.biUnion Ec)
    (hE_card : E.card = Fintype.card V * k) (hE_loop : ∀ e ∈ E, ¬ e.IsDiag)
    {c₁ c₂ : {c : C // c ∈ C₀}} (hne : c₁ ≠ c₂) {v : V}
    (hv₁ : (929 / 1000 : ℝ) * (k : ℝ) ≤ (degE (Ec c₁) v : ℝ))
    (hv₂ : (929 / 1000 : ℝ) * (k : ℝ) ≤ (degE (Ec c₂) v : ℝ)) : False := by
  let n := Fintype.card V
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  let S₁ := Finset.univ.filter fun u : V => hasEdge (Ec c₁) v u
  let S₂ := Finset.univ.filter fun u : V => hasEdge (Ec c₂) v u
  have hS_disj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]; intro u hu1 hu2
    have h1 := (Finset.mem_filter.mp hu1).2.2
    have h2' := (Finset.mem_filter.mp hu2).2.2
    have hne' : c₁.1 ≠ c₂.1 := fun h => hne (Subtype.ext h)
    exact Finset.disjoint_left.mp (G.disjoint_colorEdges hne') (hEc_sub c₁ h1) (hEc_sub c₂ h2')
  let Cross := (S₁ ×ˢ S₂).filter fun p => hasEdge E p.1 p.2
  let NonAdjCross := (S₁ ×ˢ S₂).filter fun p => ¬ hasEdge E p.1 p.2
  have hOut_card : ∀ (c : {c : C // c ∈ C₀}),
      ((Ec c).filter fun e => ¬ (v ∈ e)).card = k - degE (Ec c) v := by
    intro c
    have htot := card_filter_add_not (Ec c) (fun e => v ∈ e)
    rw [card_incident_edges (Ec c) (hEc_loop c) v, hEc_card c] at htot; omega
  have hCross_card : Cross.card ≤ (k - S₁.card) + (k - S₂.card) := by
    let Out₁ := (Ec c₁).filter fun e => ¬ (v ∈ e)
    let Out₂ := (Ec c₂).filter fun e => ¬ (v ∈ e)
    have hmap : Cross.card ≤ (Out₁ ∪ Out₂).card := by
      refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
      · intro ⟨x, y⟩ hp
        rcases Finset.mem_filter.mp hp with ⟨hprod, hxy⟩
        rcases Finset.mem_product.mp hprod with ⟨hx, hy⟩
        have hx1 := (Finset.mem_filter.mp hx).2
        have hy2 := (Finset.mem_filter.mp hy).2
        have hv_not : ¬ (v ∈ s(x, y)) := fun hv => by
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact hx1.1 rfl
          · exact hy2.1 rfl
        have hxyE : s(x, y) ∈ C₀.attach.biUnion Ec := hE_def ▸ hxy.2
        rcases Finset.mem_biUnion.mp hxyE with ⟨c₃, _, h3⟩
        have h1G := (G.mem_colorEdges_mk).mp (hEc_sub c₁ hx1.2)
        have h2G := (G.mem_colorEdges_mk).mp (hEc_sub c₂ hy2.2)
        have h3G := (G.mem_colorEdges_mk).mp (hEc_sub c₃ h3)
        have hc3 : c₃ = c₁ ∨ c₃ = c₂ := by
          by_contra hne3; push Not at hne3
          have hne12 : c₁.1 ≠ c₂.1 := fun h => hne (Subtype.ext h)
          exact hno_rb ⟨v, x, y, h1G.1, h3G.1, G.symm _ _ h2G.1,
            by rw [h1G.2, h3G.2]; exact fun e => hne3.1 (Subtype.ext e.symm),
            by rw [h3G.2, G.color_symm y v, h2G.2]; exact fun e => hne3.2 (Subtype.ext e),
            by rw [G.color_symm y v, h2G.2, h1G.2]; exact hne12.symm⟩
        rcases hc3 with rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h3, hv_not⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h3, hv_not⟩)
      · intro ⟨x, y⟩ hp₁ ⟨x', y'⟩ hp₂ heq
        have hx := (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).1
        have hy' := (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).2
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact (Finset.disjoint_left.mp hS_disj hx hy').elim
    calc Cross.card ≤ (Out₁ ∪ Out₂).card := hmap
      _ ≤ Out₁.card + Out₂.card := Finset.card_union_le _ _
      _ = (k - S₁.card) + (k - S₂.card) := by rw [hOut_card c₁, hOut_card c₂]; rfl
  have hNonAdj_le : 2 * E.card + 2 * NonAdjCross.card ≤ n * (n - 1) := by
    let OrdAll := (Finset.univ ×ˢ Finset.univ : Finset (V × V)).filter fun p : V × V => p.1 ≠ p.2
    let OrdE := Finset.univ.filter fun p : V × V => hasEdge E p.1 p.2
    let NA2 := NonAdjCross.map ⟨Prod.swap, Prod.swap_injective⟩
    have hsub1 : OrdE ⊆ OrdAll := fun p hp =>
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hp).2.1⟩
    have hsub2 : NonAdjCross ⊆ OrdAll := fun p hp => by
      have hpr := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        fun h => Finset.disjoint_left.mp hS_disj hpr.1 (h ▸ hpr.2)⟩
    have hsub3 : NA2 ⊆ OrdAll := fun p hp => by
      rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
      have hpr := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        fun h => Finset.disjoint_left.mp hS_disj hpr.1 ((show q.2 = q.1 from h) ▸ hpr.2)⟩
    have hd1 : Disjoint OrdE NonAdjCross := Finset.disjoint_left.mpr fun p h1 h2 =>
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hd2 : Disjoint (OrdE ∪ NonAdjCross) NA2 := Finset.disjoint_left.mpr fun p h1 h2 => by
      rcases Finset.mem_map.mp h2 with ⟨q, hq, rfl⟩
      rcases Finset.mem_union.mp h1 with hE | hN1
      · exact (Finset.mem_filter.mp hq).2 (hasEdge_symm.mp (Finset.mem_filter.mp hE).2)
      · have h1p := Finset.mem_product.mp (Finset.mem_filter.mp hN1).1
        have h2p := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
        exact Finset.disjoint_left.mp hS_disj h1p.1 h2p.2
    have hle := Finset.card_le_card (Finset.union_subset (Finset.union_subset hsub1 hsub2) hsub3)
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_map] at hle
    have hOrdE_c : OrdE.card = 2 * E.card := by
      rw [← sym2_card_double E hE_loop]
      simp only [OrdE, degE, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    have hOrdAll_c : OrdAll.card = n * (n - 1) := by
      have := card_pair_diff (Finset.univ : Finset V)
      rw [Finset.card_univ] at this; exact this
    rw [hOrdE_c, hOrdAll_c] at hle; omega
  have hCross_add : Cross.card + NonAdjCross.card = S₁.card * S₂.card := by
    have hu := card_filter_add_not (S₁ ×ˢ S₂) (fun p : V × V => hasEdge E p.1 p.2)
    rw [Finset.card_product] at hu; exact hu
  have hS1_le_k : S₁.card ≤ k := by
    change degE (Ec c₁) v ≤ k
    rw [← hEc_card c₁, ← card_incident_edges (Ec c₁) (hEc_loop c₁) v]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hS2_le_k : S₂.card ≤ k := by
    change degE (Ec c₂) v ≤ k
    rw [← hEc_card c₂, ← card_incident_edges (Ec c₂) (hEc_loop c₂) v]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hNA_r : (929 / 1000 : ℝ) ^ 2 * (k : ℝ) ^ 2 - 2 * (71 / 1000 : ℝ) * (k : ℝ) ≤ (NonAdjCross.card : ℝ) := by
    have h1 : (Cross.card : ℝ) ≤ ((k : ℝ) - (S₁.card : ℝ)) + ((k : ℝ) - (S₂.card : ℝ)) := by
      have hnat : (Cross.card : ℝ) ≤ (((k - S₁.card) + (k - S₂.card) : ℕ) : ℝ) := by exact_mod_cast hCross_card
      push_cast [Nat.cast_sub hS1_le_k, Nat.cast_sub hS2_le_k] at hnat; linarith
    have h2' : (Cross.card : ℝ) + (NonAdjCross.card : ℝ) = (S₁.card : ℝ) * (S₂.card : ℝ) := by
      have hcast : ((Cross.card + NonAdjCross.card : ℕ) : ℝ) = ((S₁.card * S₂.card : ℕ) : ℝ) := by
        exact_mod_cast hCross_add
      push_cast at hcast; exact hcast
    have hS1_r : (929 / 1000 : ℝ) * (k : ℝ) ≤ (S₁.card : ℝ) := hv₁
    have hS2_r : (929 / 1000 : ℝ) * (k : ℝ) ≤ (S₂.card : ℝ) := hv₂
    nlinarith
  have hE_r : 2 * ((n : ℝ) * (k : ℝ)) + 2 * (NonAdjCross.card : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [hE_card] at hNonAdj_le
    have h1 : ((2 * (n * k) + 2 * NonAdjCross.card : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
      exact_mod_cast hNonAdj_le
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h1; linarith
  let t₁ : ℝ := (k : ℝ) / (n : ℝ)
  have ht_le_t1 : t ≤ t₁ := by dsimp [t₁]; rw [le_div_iff₀ hn_r]; exact hk_ge
  have ht1_lt_half : t₁ < 1 / 2 := by
    dsimp [t₁]; rw [div_lt_iff₀ hn_r]
    have h1 : ((2 * k : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h2k_le
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h1; linarith
  have hk_eq : (k : ℝ) = t₁ * (n : ℝ) := by dsimp [t₁]; exact (div_mul_cancel₀ _ hn_r.ne').symm
  rw [hk_eq] at hNA_r hE_r
  have hsq_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_r
  have hcontra_t1 : t₁ ≤ 1 / 2 - (929 / 1000 : ℝ) ^ 2 * t₁ ^ 2 := by
    by_contra hgt; push Not at hgt
    have : (n : ℝ) ^ 2 * (1 / 2 - (929 / 1000 : ℝ) ^ 2 * t₁ ^ 2) < (n : ℝ) ^ 2 * t₁ :=
      mul_lt_mul_of_pos_left hgt hsq_pos
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr ht_le_t1) (show 0 ≤ t₁ + t by linarith)]

omit [Fintype C] [DecidableEq C] in
/-- Step 2 (Case 2): Injective concentration centers induce a `C₃`-free oriented graph contradicting `h_CH`. -/
private lemma rainbow_case_inj_center
    {c_CH t δ : ℝ}
    (h_CH : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ u : W, (H.toDigraph.outDeg u : ℝ) < c_CH * Fintype.card W)
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 2) (hδ_lt1 : δ < 1) (h1 : c_CH * (1 - δ) ≤ (929 / 1000 : ℝ) * t - δ)
    (G : EdgeColoredGraph V C) (hno_rb : ¬ G.HasRainbowTriangle)
    (C₀ : Finset C) (k : ℕ) (hk_ge : t * (Fintype.card V : ℝ) ≤ (k : ℝ))
    (Ec : {c : C // c ∈ C₀} → Finset (Sym2 V)) (hEc_sub : ∀ c, Ec c ⊆ G.colorEdges c.1)
    (Conc : Finset {c : C // c ∈ C₀})
    (hConc_gt : (1 - δ) * (Fintype.card V : ℝ) < (Conc.card : ℝ))
    (center : {c : {c : C // c ∈ C₀} // c ∈ Conc} → V)
    (hcenter : ∀ c, (929 / 1000 : ℝ) * (k : ℝ) ≤ (degE (Ec c.1) (center c) : ℝ))
    (hcenter_inj : Function.Injective center) : False := by
  let n := Fintype.card V
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let T : Finset V := Finset.univ.image center
  have hT_card : T.card = Conc.card := by
    rw [Finset.card_image_of_injective _ hcenter_inj, Finset.card_univ, Fintype.card_coe]
  have hT_gt : (1 - δ) * (n : ℝ) < (T.card : ℝ) := by rw [hT_card]; exact hConc_gt
  have hT_ne : T.Nonempty := by
    have : (0 : ℝ) < (T.card : ℝ) := lt_of_le_of_lt (by nlinarith) hT_gt
    exact Finset.card_pos.mp (by exact_mod_cast this)
  have _ : Nonempty {x : V // x ∈ T} := hT_ne.to_subtype
  have hex_col : ∀ u : {x : V // x ∈ T}, ∃ c : {c : {c : C // c ∈ C₀} // c ∈ Conc}, center c = u.1 := by
    intro ⟨x, hx⟩
    rcases Finset.mem_image.mp hx with ⟨c, _, rfl⟩
    exact ⟨c, rfl⟩
  choose colOf hcolOf using hex_col
  have hcolOf_inj : Function.Injective colOf := fun u₁ u₂ heq =>
    Subtype.ext (by rw [← hcolOf u₁, ← hcolOf u₂, heq])
  let D : OrientedGraph {x : V // x ∈ T} :=
    { adj := fun u w => hasEdge (Ec (colOf u).1) u.1 w.1
      loopless := fun u h => h.1 rfl
      asymm := fun u w huw hwu => by
        have hne_uw : u ≠ w := fun h => huw.1 (congrArg Subtype.val h)
        have hne_c : (colOf u).1.1 ≠ (colOf w).1.1 := fun h =>
          hne_uw (hcolOf_inj (Subtype.ext (Subtype.ext h)))
        have h1' := (G.mem_colorEdges_mk).mp (hEc_sub (colOf u).1 huw.2)
        have h2' := (G.mem_colorEdges_mk).mp (hEc_sub (colOf w).1 hwu.2)
        rw [G.color_symm] at h2'
        exact hne_c (h1'.2.symm.trans h2'.2) }
  have hD_tri : D.TriangleFree := by
    rintro ⟨u, w, z, huw, hwz, hzu⟩
    have h1' := (G.mem_colorEdges_mk).mp (hEc_sub (colOf u).1 huw.2)
    have h2' := (G.mem_colorEdges_mk).mp (hEc_sub (colOf w).1 hwz.2)
    have h3' := (G.mem_colorEdges_mk).mp (hEc_sub (colOf z).1 hzu.2)
    have hne_uw : u ≠ w := fun h => huw.1 (congrArg Subtype.val h)
    have hne_wz : w ≠ z := fun h => hwz.1 (congrArg Subtype.val h)
    have hne_zu : z ≠ u := fun h => hzu.1 (congrArg Subtype.val h)
    exact hno_rb ⟨u.1, w.1, z.1, h1'.1, h2'.1, h3'.1,
      by rw [h1'.2, h2'.2]; exact fun e => hne_uw (hcolOf_inj (Subtype.ext (Subtype.ext e))),
      by rw [h2'.2, h3'.2]; exact fun e => hne_wz (hcolOf_inj (Subtype.ext (Subtype.ext e))),
      by rw [h3'.2, h1'.2]; exact fun e => hne_zu (hcolOf_inj (Subtype.ext (Subtype.ext e)))⟩
  obtain ⟨u, hu_lt⟩ := h_CH D hD_tri
  have hu_deg_ge : (929 / 1000 : ℝ) * (k : ℝ) - ((n : ℝ) - (T.card : ℝ)) ≤ (D.toDigraph.outDeg u : ℝ) := by
    let Nu := Finset.univ.filter fun w : V => hasEdge (Ec (colOf u).1) u.1 w
    have hNu_ge : (929 / 1000 : ℝ) * (k : ℝ) ≤ (Nu.card : ℝ) := by
      have := hcenter (colOf u); rwa [hcolOf u] at this
    have hmap : (D.toDigraph.outSet u).card = (Nu ∩ T).card := by
      refine Finset.card_bij (fun w _ => w.1)
        (fun w hw => Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Digraph.mem_outSet _).mp hw⟩, w.2⟩)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun x hx => ⟨⟨x, (Finset.mem_inter.mp hx).2⟩,
          (Digraph.mem_outSet _).mpr (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2, rfl⟩)
    have hunion := Finset.card_union_add_card_inter Nu T
    have hle_n : (Nu ∪ T).card ≤ n := Finset.card_le_univ _
    have hnat : Nu.card + T.card ≤ n + (D.toDigraph.outDeg u) := by
      change Nu.card + T.card ≤ n + (D.toDigraph.outSet u).card
      rw [hmap]; omega
    have hreal : ((Nu.card + T.card : ℕ) : ℝ) ≤ ((n + D.toDigraph.outDeg u : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal; linarith
  have hT_le_n : (T.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast Finset.card_le_univ T
  have hT_coe : (Fintype.card {x : V // x ∈ T} : ℝ) = (T.card : ℝ) := by exact_mod_cast Fintype.card_coe T
  rw [hT_coe] at hu_lt
  have hc_le1 : c_CH ≤ 1 := by nlinarith
  nlinarith

end HompeQuSpirkl

open Classical in
/-- **Parameterized Hompe–Qu–Spirkl Theorem 3 (`arXiv:2206.10733`, Zero-DP Pure-Kernel Proof)**:
Suppose every finite nonempty `C₃`-free oriented graph satisfies `∃ u, outDeg u < c_CH · |V|`.
For `ε = 71/1000` and ANY `δ ∈ (0, 1)`, `t ∈ [79/200, 1/2]` satisfying:
1. `c_CH * (1 - δ) ≤ (929 / 1000) * t - δ`,
2. `1 / 2 - (929 / 1000) ^ 2 * t ^ 2 < t`,
3. `(1 - δ * (2 * (71 / 1000) - 2 * (71 / 1000) ^ 2)) * t < (8 / 3) * (t - 1 / 4)`,
every finite simple edge-colored graph on `n ≥ 1` vertices with at least `n` color classes each
containing at least `t · n` edges contains a rainbow triangle! -/
theorem rainbow_triangle_of_ch_bound
    {c_CH t δ : ℝ}
    (h_CH : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ u : W, (H.toDigraph.outDeg u : ℝ) < c_CH * Fintype.card W)
    (ht_lo : 79 / 200 ≤ t) (ht_hi : t ≤ 1 / 2) (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1)
    (h1 : c_CH * (1 - δ) ≤ (929 / 1000 : ℝ) * t - δ)
    (h2 : 1 / 2 - (929 / 1000 : ℝ) ^ 2 * t ^ 2 < t)
    (h3 : (1 - δ * (2 * (71 / 1000 : ℝ) - 2 * (71 / 1000 : ℝ) ^ 2)) * t < (8 / 3 : ℝ) * (t - 1 / 4))
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C)
    (hC_card : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, t * (Fintype.card V : ℝ) ≤ ((G.colorEdges c).card : ℝ)) :
    G.HasRainbowTriangle := by
  classical
  by_contra hno_rb
  let n : ℕ := Fintype.card V
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  obtain ⟨C₀, _, hC₀_card⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset C))
    (n := n) (by rw [Finset.card_univ]; exact hC_card)
  let k : ℕ := Nat.ceil (t * (n : ℝ))
  have hk_ge : t * (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hex_sub : ∀ c ∈ C₀, ∃ Ec : Finset (Sym2 V), Ec ⊆ G.colorEdges c ∧ Ec.card = k := fun c _ =>
    Finset.exists_subset_card_eq (Nat.ceil_le.mpr (hsize c))
  choose Ec hEc_sub hEc_card using fun c : {c : C // c ∈ C₀} => hex_sub c.1 c.2
  let E : Finset (Sym2 V) := C₀.attach.biUnion Ec
  have hEc_disj : Set.PairwiseDisjoint (C₀.attach : Set {c : C // c ∈ C₀}) Ec := by
    intro c₁ _ c₂ _ hne
    exact (G.disjoint_colorEdges (fun h => hne (Subtype.ext h))).mono (hEc_sub c₁) (hEc_sub c₂)
  have hE_card : E.card = n * k := by
    rw [Finset.card_biUnion hEc_disj]
    calc ∑ c ∈ C₀.attach, (Ec c).card = ∑ _c ∈ C₀.attach, k := Finset.sum_congr rfl fun c _ => hEc_card c
      _ = C₀.attach.card * k := by rw [Finset.sum_const, smul_eq_mul]
      _ = n * k := by rw [Finset.card_attach, hC₀_card]
  have hE_loop : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨c, _, hec⟩
    have heG : e ∈ G.edgeFinset := G.colorEdges_subset c.1 (hEc_sub c hec)
    induction e using Sym2.ind with
    | _ x y =>
      intro hd; have hxy : x = y := Sym2.mk_isDiag_iff.mp hd; subst hxy
      exact G.loopless x ((G.mem_edgeFinset_mk).mp heG)
  have hEc_loop : ∀ c : {c : C // c ∈ C₀}, ∀ e ∈ Ec c, ¬ e.IsDiag :=
    fun c e he => hE_loop e (Finset.mem_biUnion.mpr ⟨c, Finset.mem_attach _ _, he⟩)
  have h2E_le : 2 * E.card ≤ n * (n - 1) := by
    rw [← sym2_card_double E hE_loop]
    have hdeg_le : ∀ x : V, degE E x ≤ n - 1 := fun x => by
      have hsub : Finset.univ.filter (fun y => hasEdge E x y) ⊆ Finset.univ.erase x := fun y hy =>
        Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hy).2.1.symm, Finset.mem_univ y⟩
      calc degE E x ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
        _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    calc ∑ x : V, degE E x ≤ ∑ _x : V, (n - 1) := Finset.sum_le_sum fun x _ => hdeg_le x
      _ = n * (n - 1) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h2k_le : 2 * k ≤ n - 1 := by
    rw [hE_card] at h2E_le
    have hmul : n * (2 * k) ≤ n * (n - 1) := by linarith
    exact Nat.le_of_mul_le_mul_left hmul hn_pos
  have htri_le : ordTriangles E ≤ ∑ c ∈ C₀.attach, ordHappyTriples (Ec c) := by
    let Tset := Finset.univ.filter fun q : V × V × V =>
      hasEdge E q.1 q.2.1 ∧ hasEdge E q.2.1 q.2.2 ∧ hasEdge E q.2.2 q.1
    let Hset (c : {c : C // c ∈ C₀}) := Finset.univ.filter fun q : V × V × V =>
      q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2 ∧ q.2.2 ≠ q.1 ∧
      ((hasEdge (Ec c) q.1 q.2.1 ∧ hasEdge (Ec c) q.2.1 q.2.2) ∨
       (hasEdge (Ec c) q.2.1 q.2.2 ∧ hasEdge (Ec c) q.2.2 q.1) ∨
       (hasEdge (Ec c) q.2.2 q.1 ∧ hasEdge (Ec c) q.1 q.2.1))
    have hcov : Tset ⊆ C₀.attach.biUnion Hset := by
      intro ⟨x, y, z⟩ hq
      rcases (Finset.mem_filter.mp hq).2 with ⟨hxy, hyz, hzx⟩
      rcases Finset.mem_biUnion.mp hxy.2 with ⟨c₁, _, h1'⟩
      rcases Finset.mem_biUnion.mp hyz.2 with ⟨c₂, _, h2'⟩
      rcases Finset.mem_biUnion.mp hzx.2 with ⟨c₃, _, h3'⟩
      have h1G := (G.mem_colorEdges_mk).mp (hEc_sub c₁ h1')
      have h2G := (G.mem_colorEdges_mk).mp (hEc_sub c₂ h2')
      have h3G := (G.mem_colorEdges_mk).mp (hEc_sub c₃ h3')
      have hnot_all_diff : c₁ = c₂ ∨ c₂ = c₃ ∨ c₃ = c₁ := by
        by_contra hall; push Not at hall; rcases hall with ⟨h12, h23, h31⟩
        exact hno_rb ⟨x, y, z, h1G.1, h2G.1, h3G.1,
          by rw [h1G.2, h2G.2]; exact fun e => h12 (Subtype.ext e),
          by rw [h2G.2, h3G.2]; exact fun e => h23 (Subtype.ext e),
          by rw [h3G.2, h1G.2]; exact fun e => h31 (Subtype.ext e)⟩
      rcases hnot_all_diff with rfl | rfl | rfl
      · exact Finset.mem_biUnion.mpr ⟨c₁, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.1, hyz.1, hzx.1, Or.inl ⟨⟨hxy.1, h1'⟩, ⟨hyz.1, h2'⟩⟩⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨c₂, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.1, hyz.1, hzx.1, Or.inr (Or.inl ⟨⟨hyz.1, h2'⟩, ⟨hzx.1, h3'⟩⟩)⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨c₃, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.1, hyz.1, hzx.1, Or.inr (Or.inr ⟨⟨hzx.1, h3'⟩, ⟨hxy.1, h1'⟩⟩)⟩⟩
    exact le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
  have hk_ge3 : 3 ≤ k := by
    by_contra hlt3
    have hk_le2 : k ≤ 2 := by omega
    have hkr : (79 / 200 : ℝ) * (n : ℝ) ≤ (k : ℝ) := le_trans (by nlinarith) hk_ge
    have hn_le5 : n ≤ 5 := by
      by_contra h6
      have h6r : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 6 ≤ n by omega)
      have h2r : (k : ℝ) ≤ 2 := by exact_mod_cast hk_le2
      linarith
    have hk12 : k = 1 ∨ k = 2 := by
      have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (by positivity) hkr
      have hk_pos : 1 ≤ k := by exact_mod_cast this
      omega
    rcases hk12 with hk1 | hk2
    · have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
      have : (k : ℝ) = 1 := by exact_mod_cast hk1
      linarith
    · have hn5 : n = 5 := by omega
      have hgd := goodman_ordTriangles E hE_loop
      have hsum_ub : ∑ c ∈ C₀.attach, ordHappyTriples (Ec c) ≤ 5 * (3 * (2 * (2 - 1))) := by
        calc ∑ c ∈ C₀.attach, ordHappyTriples (Ec c)
            ≤ ∑ _c ∈ C₀.attach, (3 * (2 * (2 - 1))) := Finset.sum_le_sum fun c _ => by
              have h := ordHappyTriples_le_three_k_mul (Ec c)
              rw [hEc_card c, hk2] at h; exact h
          _ = C₀.attach.card * (3 * (2 * (2 - 1))) := by rw [Finset.sum_const, smul_eq_mul]
          _ = 5 * (3 * (2 * (2 - 1))) := by rw [Finset.card_attach, hC₀_card, hn5]
      have hE10 : E.card = 10 := by rw [hE_card, hk2, hn5]
      have hcardV5 : Fintype.card V = 5 := hn5
      rw [hE10, hcardV5] at hgd
      have htr : (ordTriangles E : ℝ) ≤ 30 := by
        have hnat : ordTriangles E ≤ 30 := le_trans htri_le hsum_ub
        exact_mod_cast hnat
      norm_num at hgd
      linarith
  have hConc_gt := rainbow_claim_conc_gt hδ_pos h3 C₀ hC₀_card k hk_ge3 hk_ge Ec hEc_card hEc_loop E hE_card hE_loop htri_le
  let Conc := C₀.attach.filter fun c => ∃ v : V, (929 / 1000 : ℝ) * (k : ℝ) ≤ (degE (Ec c) v : ℝ)
  choose center hcenter using fun c : {c : {c : C // c ∈ C₀} // c ∈ Conc} => (Finset.mem_filter.mp c.2).2
  by_cases hshared : ∃ c₁ c₂ : {c : {c : C // c ∈ C₀} // c ∈ Conc}, c₁ ≠ c₂ ∧ center c₁ = center c₂
  · rcases hshared with ⟨c₁, c₂, hne, heq_v⟩
    exact rainbow_case_shared_center (by linarith) h2 G hno_rb C₀ k hk_ge h2k_le Ec hEc_sub hEc_card hEc_loop
      E rfl hE_card hE_loop (fun h => hne (Subtype.ext h)) (hcenter c₁) (heq_v ▸ hcenter c₂)
  · push Not at hshared
    have hinj : Function.Injective center := fun c₁ c₂ heq => by
      by_contra hne; exact hshared c₁ c₂ hne heq
    exact rainbow_case_inj_center h_CH (by linarith) ht_hi hδ_lt1 h1 G hno_rb C₀ k hk_ge Ec hEc_sub
      Conc hConc_gt center hcenter hinj

/-- Rainbow triangle bound assuming the oriented-graph out-degree bound `677/2000`. -/
theorem rainbow_triangle_797_2000
    (h_CH : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ u : W, (H.toDigraph.outDeg u : ℝ) < (677 / 2000 : ℝ) * Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C)
    (hC_card : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, (797 / 2000 : ℝ) * (Fintype.card V : ℝ) ≤ ((G.colorEdges c).card : ℝ)) :
    G.HasRainbowTriangle :=
  rainbow_triangle_of_ch_bound (c_CH := 677 / 2000) (t := 797 / 2000) (δ := 479 / 10000)
    h_CH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G hC_card hsize

/-- Rainbow triangle bound assuming the oriented-graph out-degree bound `4229/12500`. -/
theorem rainbow_triangle_39849_100000
    (h_CH : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ u : W, (H.toDigraph.outDeg u : ℝ) < (4229 / 12500 : ℝ) * Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C)
    (hC_card : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, (39849 / 100000 : ℝ) * (Fintype.card V : ℝ) ≤ ((G.colorEdges c).card : ℝ)) :
    G.HasRainbowTriangle :=
  rainbow_triangle_of_ch_bound (c_CH := 4229 / 12500) (t := 39849 / 100000) (δ := 481 / 10000)
    h_CH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G hC_card hsize

/-- Rainbow triangle bound assuming the oriented-graph out-degree bound `3383/10000`. -/
theorem rainbow_triangle_79697_200000
    (h_CH : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (H : OrientedGraph W) [DecidableRel H.adj],
      H.TriangleFree → ∃ u : W, (H.toDigraph.outDeg u : ℝ) < (3383 / 10000 : ℝ) * Fintype.card W)
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (G : EdgeColoredGraph V C)
    (hC_card : Fintype.card V ≤ Fintype.card C)
    (hsize : ∀ c : C, (79697 / 200000 : ℝ) * (Fintype.card V : ℝ) ≤ ((G.colorEdges c).card : ℝ)) :
    G.HasRainbowTriangle :=
  rainbow_triangle_of_ch_bound (c_CH := 3383 / 10000) (t := 79697 / 200000) (δ := 4817 / 100000)
    h_CH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G hC_card hsize

end CaccettaHaggkvist
