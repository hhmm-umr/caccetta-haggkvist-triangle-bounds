module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Basic Definitions for Directed Graphs and the Caccetta–Häggkvist Conjecture

This module defines:
* `Digraph V`: a simple directed graph (irreflexive binary adjacency relation, no self-loops).
* `Digraph.HasDigon G`: existence of a directed 2-cycle `u → v → u`.
* `Digraph.HasDirTriangle G`: existence of a directed 3-cycle `u → v → w → u`.
* `Digraph.HasCycleLe3 G`: existence of a directed cycle of length at most 3 (2-cycle or 3-cycle,
  since 1-cycles are forbidden by `loopless`).
* `OrientedGraph V`: a simple oriented graph (`Digraph V` with asymmetry `adj u v → ¬ adj v u`).
* Out-neighborhoods, in-neighborhoods, out-degrees, in-degrees, and the exact reduction from
  general simple digraphs to `C₃`-free oriented graphs.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

/-- A simple directed graph on vertex type `V` (irreflexive: no self-loops).
Digons (`adj u v ∧ adj v u`) are permitted in `Digraph` and count as directed 2-cycles. -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v

namespace Digraph

variable {V : Type*}

lemma ne_of_adj (G : Digraph V) {u v : V} (h : G.adj u v) : u ≠ v := by
  rintro rfl
  exact G.loopless u h

/-- `G` contains a directed 2-cycle (digon) `u → v → u`. -/
def HasDigon (G : Digraph V) : Prop :=
  ∃ u v : V, G.adj u v ∧ G.adj v u

/-- `G` contains a directed 3-cycle (directed triangle) `u → v → w → u`. -/
def HasDirTriangle (G : Digraph V) : Prop :=
  ∃ u v w : V, G.adj u v ∧ G.adj v w ∧ G.adj w u

/-- `G` contains a directed cycle of length at most 3. Since `G` is loopless, any directed cycle
has length at least 2, so this is equivalent to having a directed 2-cycle or a directed 3-cycle. -/
def HasCycleLe3 (G : Digraph V) : Prop :=
  G.HasDigon ∨ G.HasDirTriangle

/-- Every directed triangle in a loopless digraph automatically has pairwise distinct vertices. -/
lemma hasDirTriangle_iff_distinct (G : Digraph V) :
    G.HasDirTriangle ↔
      ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.adj u v ∧ G.adj v w ∧ G.adj w u := by
  constructor
  · rintro ⟨u, v, w, huv, hvw, hwu⟩
    exact ⟨u, v, w, G.ne_of_adj huv, G.ne_of_adj hvw, G.ne_of_adj hwu, huv, hvw, hwu⟩
  · rintro ⟨u, v, w, -, -, -, huv, hvw, hwu⟩
    exact ⟨u, v, w, huv, hvw, hwu⟩

/-- Every digon in a loopless digraph automatically has distinct vertices. -/
lemma hasDigon_iff_distinct (G : Digraph V) :
    G.HasDigon ↔ ∃ u v : V, u ≠ v ∧ G.adj u v ∧ G.adj v u := by
  constructor
  · rintro ⟨u, v, huv, hvu⟩
    exact ⟨u, v, G.ne_of_adj huv, huv, hvu⟩
  · rintro ⟨u, v, -, huv, hvu⟩
    exact ⟨u, v, huv, hvu⟩

/-- Out-neighborhood `{v | G.adj u v}` of vertex `u` in a finite digraph `G`. -/
def outSet [Fintype V] (G : Digraph V) [DecidableRel G.adj] (u : V) : Finset V :=
  Finset.univ.filter (G.adj u)

/-- In-neighborhood `{v | G.adj v u}` of vertex `u` in a finite digraph `G`. -/
def inSet [Fintype V] (G : Digraph V) [DecidableRel G.adj] (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.adj v u)

/-- Out-degree `|N⁺(u)|` of vertex `u` in a finite digraph `G`. -/
def outDeg [Fintype V] (G : Digraph V) [DecidableRel G.adj] (u : V) : ℕ :=
  (G.outSet u).card

/-- In-degree `|N⁻(u)|` of vertex `u` in a finite digraph `G`. -/
def inDeg [Fintype V] (G : Digraph V) [DecidableRel G.adj] (u : V) : ℕ :=
  (G.inSet u).card

@[simp]
lemma mem_outSet [Fintype V] (G : Digraph V) [DecidableRel G.adj] {u v : V} :
    v ∈ G.outSet u ↔ G.adj u v := by
  simp [outSet]

@[simp]
lemma mem_inSet [Fintype V] (G : Digraph V) [DecidableRel G.adj] {u v : V} :
    v ∈ G.inSet u ↔ G.adj v u := by
  simp [inSet]

lemma notMem_outSet_self [Fintype V] (G : Digraph V) [DecidableRel G.adj] (u : V) :
    u ∉ G.outSet u := by
  simp [G.loopless u]

lemma notMem_inSet_self [Fintype V] (G : Digraph V) [DecidableRel G.adj] (u : V) :
    u ∉ G.inSet u := by
  simp [G.loopless u]

/-- `outDeg` is independent of the `DecidableRel` instance. -/
lemma outDeg_congr [Fintype V] (G : Digraph V) (d₁ d₂ : DecidableRel G.adj) (u : V) :
    @outDeg V _ G d₁ u = @outDeg V _ G d₂ u := by
  unfold outDeg outSet
  congr 1
  ext v
  simp

/-- Handshaking lemma for finite digraphs: `∑ u, outDeg u = ∑ u, inDeg u`. -/
lemma sum_outDeg_eq_sum_inDeg [Fintype V] (G : Digraph V) [DecidableRel G.adj] :
    ∑ u : V, G.outDeg u = ∑ u : V, G.inDeg u := by
  simp only [outDeg, inDeg, outSet, inSet, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

end Digraph

/-- An oriented graph on `V` is a loopless digraph with asymmetric adjacency (`¬ (u → v ∧ v → u)`),
i.e., a digon-free simple digraph. -/
structure OrientedGraph (V : Type*) extends Digraph V where
  asymm : ∀ u v, adj u v → ¬ adj v u

namespace OrientedGraph

variable {V : Type*}

/-- An oriented graph has no digons. -/
lemma not_hasDigon (G : OrientedGraph V) : ¬ G.toDigraph.HasDigon := by
  rintro ⟨u, v, huv, hvu⟩
  exact G.asymm u v huv hvu

/-- `G` is `C₃`-free (`TriangleFree`) if its underlying digraph has no directed triangle. -/
def TriangleFree (G : OrientedGraph V) : Prop :=
  ¬ G.toDigraph.HasDirTriangle

/-- For an oriented graph, `HasCycleLe3` is equivalent to `HasDirTriangle`. -/
lemma hasCycleLe3_iff_hasDirTriangle (G : OrientedGraph V) :
    G.toDigraph.HasCycleLe3 ↔ G.toDigraph.HasDirTriangle := by
  unfold Digraph.HasCycleLe3
  exact or_iff_right G.not_hasDigon

/-- Out-neighborhood and out-degree inherited from `Digraph`, plus `outDeg + inDeg ≤ |V| - 1`. -/
lemma disjoint_outSet_inSet [Fintype V] (G : OrientedGraph V) [DecidableRel G.adj] (u : V) :
    Disjoint (G.toDigraph.outSet u) (G.toDigraph.inSet u) := by
  rw [Finset.disjoint_left]
  intro v hv_out hv_in
  rw [Digraph.mem_outSet] at hv_out
  rw [Digraph.mem_inSet] at hv_in
  exact G.asymm u v hv_out hv_in

lemma outDeg_add_inDeg_add_one_le [Fintype V] [DecidableEq V]
    (G : OrientedGraph V) [DecidableRel G.adj] (u : V) :
    G.toDigraph.outDeg u + G.toDigraph.inDeg u + 1 ≤ Fintype.card V := by
  have hdisj1 : Disjoint (G.toDigraph.outSet u) (G.toDigraph.inSet u) :=
    G.disjoint_outSet_inSet u
  have hnot : u ∉ G.toDigraph.outSet u ∪ G.toDigraph.inSet u := by
    simp [G.loopless u]
  have hcard :
      (insert u (G.toDigraph.outSet u ∪ G.toDigraph.inSet u)).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj1] at hcard
  exact hcard

end OrientedGraph

/-- Digon-free upgrade: any simple digraph without digons upgrades directly to an `OrientedGraph`
with identical adjacency relation and out-degrees. -/
def Digraph.toOrientedOfNotHasDigon {V : Type*} (G : Digraph V) (h : ¬ G.HasDigon) :
    OrientedGraph V where
  adj := G.adj
  loopless := G.loopless
  asymm := fun u v huv hvu => h ⟨u, v, huv, hvu⟩

/-- **Exact General-Digraph-to-Oriented-Graph Reduction**:
To prove that every finite simple digraph `G` on `V` (`|V| ≥ 1`) with minimum out-degree
`∀ u, (G.outDeg u : ℝ) ≥ c * |V|` has a directed cycle of length `≤ 3`, it suffices to prove that
every `C₃`-free `OrientedGraph` on `V` has some vertex `u` with `(G.outDeg u : ℝ) < c * |V|`. -/
theorem hasCycleLe3_of_oriented_bound {V : Type*} [Fintype V] [Nonempty V]
    {c : ℝ}
    (h_oriented : ∀ (H : OrientedGraph V) (d : DecidableRel H.adj),
      H.TriangleFree → ∃ u : V, (@Digraph.outDeg V _ H.toDigraph d u : ℝ) < c * Fintype.card V)
    (G : Digraph V) [dG : DecidableRel G.adj]
    (hdeg : ∀ u : V, c * Fintype.card V ≤ (G.outDeg u : ℝ)) :
    G.HasCycleLe3 := by
  by_contra hno
  have hnodigon : ¬ G.HasDigon := fun hd => hno (Or.inl hd)
  have hnotri : ¬ G.HasDirTriangle := fun ht => hno (Or.inr ht)
  let H : OrientedGraph V := G.toOrientedOfNotHasDigon hnodigon
  obtain ⟨u, hu⟩ := h_oriented H dG hnotri
  exact not_lt_of_ge (hdeg u) hu

end CaccettaHaggkvist
