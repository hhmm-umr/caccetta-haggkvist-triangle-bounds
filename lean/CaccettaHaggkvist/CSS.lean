module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical

/-!
# Chudnovsky–Seymour–Sullivan (`α_CSS = 1`) & HHK Out-Degree Bound for `C₃`-Free Oriented Graphs

This module proves unconditionally in Lean 4 (with zero `sorry` and standard axioms only):
1. **CSS Theorem 1.1 (`Chudnovsky–Seymour–Sullivan 2008`, `α_CSS = 1`)**:
   Every finite `C₃`-free oriented graph `H` admits a feedback arc set `F` (witnessed by an
   explicit injective topological rank `rank : V → ℕ` such that all remaining arcs go strictly
   downward `rank w < rank u`) satisfying `2 * F.card ≤ ordNonEdges H` (i.e., `|F| ≤ γ(H)`).
2. **Hamburger–Haxell–Kostochka Consequence (`outDeg_sq_le_ordNonEdges`)**:
   In any finite nonempty `C₃`-free oriented graph `H` where every vertex has out-degree `≥ d`,
   `d * (d + 1) ≤ ordNonEdges H` (hence `d^2 ≤ 2 * γ(H)`).
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

namespace OrientedGraph

/-- Number of ordered distinct non-adjacent vertex pairs `(x, y)` (`= 2 * γ(H)`).
Working directly with `ordNonEdges H = 2 * γ(H)` eliminates all `ℕ` division by `2`. -/
def ordNonEdges {V : Type u} [Fintype V] [DecidableEq V]
    (H : OrientedGraph V) [DecidableRel H.adj] : ℕ :=
  (Finset.univ.filter fun p : V × V => p.1 ≠ p.2 ∧ ¬ H.adj p.1 p.2 ∧ ¬ H.adj p.2 p.1).card

/-- Number of induced 2-paths starting at `v` (`v → y → z` with `v ≁ z`). -/
def twoPathStart {V : Type u} [Fintype V] [DecidableEq V]
    (H : OrientedGraph V) [DecidableRel H.adj] (v : V) : ℕ :=
  (Finset.univ.filter fun p : V × V =>
    H.adj v p.1 ∧ H.adj p.1 p.2 ∧ v ≠ p.2 ∧ ¬ H.adj v p.2 ∧ ¬ H.adj p.2 v).card

/-- Number of induced 2-paths centered at `v` (`x → v → z` with `x ≁ z`). -/
def twoPathMid {V : Type u} [Fintype V] [DecidableEq V]
    (H : OrientedGraph V) [DecidableRel H.adj] (v : V) : ℕ :=
  (Finset.univ.filter fun p : V × V =>
    H.adj p.1 v ∧ H.adj v p.2 ∧ p.1 ≠ p.2 ∧ ¬ H.adj p.1 p.2 ∧ ¬ H.adj p.2 p.1).card

lemma sum_twoPathStart_eq_sum_twoPathMid {V : Type u} [Fintype V] [DecidableEq V]
    (H : OrientedGraph V) [DecidableRel H.adj] :
    ∑ v : V, H.twoPathStart v = ∑ v : V, H.twoPathMid v := by
  simp only [twoPathStart, twoPathMid, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma exists_twoPathStart_le_twoPathMid {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : OrientedGraph V) [DecidableRel H.adj] :
    ∃ v : V, H.twoPathStart v ≤ H.twoPathMid v := by
  by_contra hno
  push Not at hno
  have hlt : ∀ v ∈ (Finset.univ : Finset V), H.twoPathMid v < H.twoPathStart v :=
    fun v _ => hno v
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
  have heq := H.sum_twoPathStart_eq_sum_twoPathMid
  omega

/-- **HHK Minimum-Out-Degree Lemma from Acyclic Ranking**:
If `rank : V → ℕ` is injective and every arc `(u, w)` outside `F` goes strictly downward
(`rank w < rank u`), then `∀ u, d ≤ outDeg u` implies `d * (d + 1) ≤ 2 * F.card`. -/
lemma deg_sq_le_two_card_feedback :
    ∀ (d : ℕ) {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
      (H : OrientedGraph V) [DecidableRel H.adj]
      (F : Finset (V × V)) (rank : V → ℕ),
      Function.Injective rank →
      (∀ u w : V, H.adj u w → (u, w) ∉ F → rank w < rank u) →
      (∀ u : V, d ≤ H.toDigraph.outDeg u) →
      d * (d + 1) ≤ 2 * F.card
  | 0, _, _, _, _, _, _, _, _, _, _, _ => by omega
  | d + 1, V, _, _, _, H, _, F, rank, h_inj, h_dag, h_deg => by
    obtain ⟨u₀, _, hu₀_min⟩ := Finset.exists_min_image Finset.univ rank Finset.univ_nonempty
    let out_u₀ : Finset (V × V) := (H.toDigraph.outSet u₀).map
      ⟨fun w => (u₀, w), fun w₁ w₂ h => by injection h⟩
    have hout_sub_F : out_u₀ ⊆ F := by
      intro p hp
      rcases Finset.mem_map.mp hp with ⟨w, hw, rfl⟩
      rw [Digraph.mem_outSet] at hw
      by_contra hnotF
      have hlt := h_dag u₀ w hw hnotF
      have hle := hu₀_min w (Finset.mem_univ w)
      omega
    have hout_card : d + 1 ≤ out_u₀.card := by
      rw [Finset.card_map]
      exact h_deg u₀
    by_cases hd0 : d = 0
    · subst hd0
      have hle : out_u₀.card ≤ F.card := Finset.card_le_card hout_sub_F
      omega
    · let S : Finset V := Finset.univ.erase u₀
      have hS_sub : H.toDigraph.outSet u₀ ⊆ S := by
        intro w hw
        exact Finset.mem_erase.mpr ⟨(H.toDigraph.ne_of_adj ((Digraph.mem_outSet H.toDigraph).mp hw)).symm,
          Finset.mem_univ w⟩
      have hS_card : d + 1 ≤ S.card := le_trans (h_deg u₀) (Finset.card_le_card hS_sub)
      have _ : Nonempty {z : V // z ∈ S} :=
        Finset.Nonempty.to_subtype (Finset.card_pos.mp (by omega))
      let subEmb : ({z : V // z ∈ S} × {z : V // z ∈ S}) ↪ V × V :=
        ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
          rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩
          rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
          injection h with ha hb
          subst ha; subst hb; rfl⟩
      let F_S : Finset ({z : V // z ∈ S} × {z : V // z ∈ S}) :=
        Finset.univ.filter fun p => (p.1.1, p.2.1) ∈ F
      have hmap_sub : F_S.map subEmb ⊆ F := by
        intro p hp
        rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
        exact (Finset.mem_filter.mp hq).2
      have hdisj : Disjoint out_u₀ (F_S.map subEmb) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rcases Finset.mem_map.mp hp1 with ⟨w, _, rfl⟩
        rcases Finset.mem_map.mp hp2 with ⟨⟨⟨a, ha⟩, _⟩, _, hpair⟩
        have ha_eq : a = u₀ := by injection hpair
        exact (Finset.mem_erase.mp ha).1 ha_eq
      have hF_split : out_u₀.card + F_S.card ≤ F.card := by
        rw [← Finset.card_map subEmb, ← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.union_subset hout_sub_F hmap_sub)
      have hdeg_S : ∀ x : {z : V // z ∈ S}, d ≤ (H.induce S).toDigraph.outDeg x := by
        intro x
        rw [H.outDeg_induce S x]
        have hx_deg : d + 1 ≤ (H.toDigraph.outSet x.1).card := h_deg x.1
        have herase_sub : (H.toDigraph.outSet x.1).erase u₀ ⊆ S ∩ H.toDigraph.outSet x.1 := by
          intro w hw
          rcases Finset.mem_erase.mp hw with ⟨hw_ne, hw_out⟩
          exact Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hw_ne, Finset.mem_univ w⟩, hw_out⟩
        have h1 : (H.toDigraph.outSet x.1).card - 1 ≤ ((H.toDigraph.outSet x.1).erase u₀).card :=
          Finset.pred_card_le_card_erase
        have h2 := Finset.card_le_card herase_sub
        omega
      have hrank_S : Function.Injective (fun x : {z : V // z ∈ S} => rank x.1) :=
        fun x y h => Subtype.ext (h_inj h)
      have hdag_S : ∀ x y : {z : V // z ∈ S},
          (H.induce S).adj x y → (x, y) ∉ F_S → rank y.1 < rank x.1 := by
        intro x y hxy hnot
        apply h_dag x.1 y.1 hxy
        intro hmem
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
      have ih := deg_sq_le_two_card_feedback d (H.induce S) F_S (fun x => rank x.1)
        hrank_S hdag_S hdeg_S
      have hcalc : (d + 1) * (d + 1 + 1) = d * (d + 1) + 2 * (d + 1) := by ring
      linarith

/-- **CSS Theorem 1.1 (`Chudnovsky–Seymour–Sullivan 2008`, `α_CSS = 1`)**:
Every finite `C₃`-free oriented graph `H` admits a feedback arc set `F` and an injective
topological ranking `rank : V → ℕ` such that `2 * F.card ≤ ordNonEdges H`. -/
theorem exists_feedback_two_card_le_ordNonEdges :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : OrientedGraph V) [DecidableRel H.adj],
      H.TriangleFree →
      ∃ (F : Finset (V × V)) (rank : V → ℕ),
        Function.Injective rank ∧
        (∀ u w : V, H.adj u w → (u, w) ∉ F → rank w < rank u) ∧
        2 * F.card ≤ H.ordNonEdges := by
  suffices hmain : ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (H : OrientedGraph V) [DecidableRel H.adj],
      Fintype.card V = n → H.TriangleFree →
      ∃ (F : Finset (V × V)) (rank : V → ℕ),
        Function.Injective rank ∧
        (∀ u w : V, H.adj u w → (u, w) ∉ F → rank w < rank u) ∧
        2 * F.card ≤ H.ordNonEdges by
    intro V _ _ H _ hH
    exact hmain (Fintype.card V) H rfl hH
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ H _ hn hH
    by_cases hne : Nonempty V
    · obtain ⟨v, hv⟩ := H.exists_twoPathStart_le_twoPathMid
      let A : Finset V := H.toDigraph.outSet v
      let BC : Finset V := (Finset.univ.erase v) \ A
      have hv_not_A : v ∉ A := H.toDigraph.notMem_outSet_self v
      have hA_lt : A.card < n := by
        rw [← hn]
        calc A.card < (insert v A).card := by rw [Finset.card_insert_of_notMem hv_not_A]; omega
          _ ≤ Fintype.card V := Finset.card_le_univ _
      have hv_not_BC : v ∉ BC := by simp [BC]
      have hBC_lt : BC.card < n := by
        rw [← hn]
        calc BC.card < (insert v BC).card := by rw [Finset.card_insert_of_notMem hv_not_BC]; omega
          _ ≤ Fintype.card V := Finset.card_le_univ _
      obtain ⟨F₁, r₁, hr₁_inj, hr₁_dag, hF₁_card⟩ :=
        ih A.card hA_lt (H.induce A) (Fintype.card_coe A) (H.triangleFree_induce hH A)
      obtain ⟨F₂, r₂, hr₂_inj, hr₂_dag, hF₂_card⟩ :=
        ih BC.card hBC_lt (H.induce BC) (Fintype.card_coe BC) (H.triangleFree_induce hH BC)
      let C : Finset V := Finset.univ.filter fun z => z ≠ v ∧ ¬ H.adj v z ∧ ¬ H.adj z v
      let EAC : Finset (V × V) := (A ×ˢ C).filter fun p => H.adj p.1 p.2
      let embA : ({z : V // z ∈ A} × {z : V // z ∈ A}) ↪ V × V :=
        ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
          rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
          injection h with ha hb; subst ha; subst hb; rfl⟩
      let embBC : ({z : V // z ∈ BC} × {z : V // z ∈ BC}) ↪ V × V :=
        ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
          rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
          injection h with ha hb; subst ha; subst hb; rfl⟩
      let F : Finset (V × V) := (F₁.map embA) ∪ (F₂.map embBC) ∪ EAC
      have hF_le : F.card ≤ F₁.card + F₂.card + EAC.card := by
        calc F.card ≤ (F₁.map embA ∪ F₂.map embBC).card + EAC.card := Finset.card_union_le _ _
          _ ≤ (F₁.map embA).card + (F₂.map embBC).card + EAC.card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ = F₁.card + F₂.card + EAC.card := by simp
      have hEAC_eq : EAC.card = H.twoPathStart v := by
        unfold EAC twoPathStart A C
        congr 1
        ext ⟨y, z⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Digraph.mem_outSet]
        tauto
      have h_nonEdges :
          (H.induce A).ordNonEdges + (H.induce BC).ordNonEdges + 2 * H.twoPathMid v ≤
            H.ordNonEdges := by
        let NE : Finset (V × V) :=
          Finset.univ.filter fun p : V × V => p.1 ≠ p.2 ∧ ¬ H.adj p.1 p.2 ∧ ¬ H.adj p.2 p.1
        let NEA_raw : Finset ({z : V // z ∈ A} × {z : V // z ∈ A}) :=
          Finset.univ.filter fun p =>
            p.1 ≠ p.2 ∧ ¬ (H.induce A).adj p.1 p.2 ∧ ¬ (H.induce A).adj p.2 p.1
        let NEBC_raw : Finset ({z : V // z ∈ BC} × {z : V // z ∈ BC}) :=
          Finset.univ.filter fun p =>
            p.1 ≠ p.2 ∧ ¬ (H.induce BC).adj p.1 p.2 ∧ ¬ (H.induce BC).adj p.2 p.1
        let NEA : Finset (V × V) := NEA_raw.map embA
        let NEBC : Finset (V × V) := NEBC_raw.map embBC
        let M1 : Finset (V × V) := Finset.univ.filter fun p : V × V =>
          H.adj p.1 v ∧ H.adj v p.2 ∧ p.1 ≠ p.2 ∧ ¬ H.adj p.1 p.2 ∧ ¬ H.adj p.2 p.1
        let M2 : Finset (V × V) := M1.map ⟨Prod.swap, Prod.swap_injective⟩
        have hsubA : NEA ⊆ NE := by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy, rfl⟩
          have hxy' := (Finset.mem_filter.mp hxy).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          refine ⟨fun h => hxy'.1 (Subtype.ext h), hxy'.2.1, hxy'.2.2⟩
        have hsubBC : NEBC ⊆ NE := by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy, rfl⟩
          have hxy' := (Finset.mem_filter.mp hxy).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          refine ⟨fun h => hxy'.1 (Subtype.ext h), hxy'.2.1, hxy'.2.2⟩
        have hsubM1 : M1 ⊆ NE := by
          intro p hp
          simp only [M1, NE, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
        have hsubM2 : M2 ⊆ NE := by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨⟨x, z⟩, hxz, rfl⟩
          simp only [M1, NE, Finset.mem_filter, Finset.mem_univ, true_and] at hxz ⊢
          exact ⟨hxz.2.2.1.symm, hxz.2.2.2.2, hxz.2.2.2.1⟩
        have h_in_A : ∀ p ∈ NEA, p.1 ∈ A ∧ p.2 ∈ A := by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, _, rfl⟩
          exact ⟨hx, hy⟩
        have h_in_BC : ∀ p ∈ NEBC, p.1 ∈ BC ∧ p.2 ∈ BC := by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, _, rfl⟩
          exact ⟨hx, hy⟩
        have h_in_M1 : ∀ p ∈ M1, p.1 ∈ BC ∧ p.2 ∈ A := by
          intro p hp
          simp only [M1, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨H.toDigraph.ne_of_adj hp.1,
            Finset.mem_univ _⟩, ?_⟩, (Digraph.mem_outSet H.toDigraph).mpr hp.2.1⟩
          rw [Digraph.mem_outSet]
          exact H.asymm p.1 v hp.1
        have h_in_M2 : ∀ p ∈ M2, p.1 ∈ A ∧ p.2 ∈ BC := by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
          exact ⟨(h_in_M1 q hq).2, (h_in_M1 q hq).1⟩
        have hA_BC_disj : ∀ x, x ∈ A → x ∈ BC → False :=
          fun x hxA hxBC => (Finset.mem_sdiff.mp hxBC).2 hxA
        have hd1 : Disjoint NEA NEBC := Finset.disjoint_left.mpr fun p hp1 hp2 =>
          hA_BC_disj p.1 (h_in_A p hp1).1 (h_in_BC p hp2).1
        have hd2 : Disjoint (NEA ∪ NEBC) M1 := Finset.disjoint_left.mpr fun p hp1 hp2 => by
          rcases Finset.mem_union.mp hp1 with hA | hBC
          · exact hA_BC_disj p.1 (h_in_A p hA).1 (h_in_M1 p hp2).1
          · exact hA_BC_disj p.2 (h_in_M1 p hp2).2 (h_in_BC p hBC).2
        have hd3 : Disjoint (NEA ∪ NEBC ∪ M1) M2 := Finset.disjoint_left.mpr fun p hp1 hp2 => by
          rcases Finset.mem_union.mp hp1 with h12 | hM1
          · rcases Finset.mem_union.mp h12 with hA | hBC
            · exact hA_BC_disj p.2 (h_in_A p hA).2 (h_in_M2 p hp2).2
            · exact hA_BC_disj p.1 (h_in_M2 p hp2).1 (h_in_BC p hBC).1
          · exact hA_BC_disj p.1 (h_in_M2 p hp2).1 (h_in_M1 p hM1).1
        have hunion_sub : NEA ∪ NEBC ∪ M1 ∪ M2 ⊆ NE :=
          Finset.union_subset (Finset.union_subset (Finset.union_subset hsubA hsubBC) hsubM1) hsubM2
        have hcard := Finset.card_le_card hunion_sub
        rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
          Finset.card_union_of_disjoint hd1] at hcard
        have hNEA_c : NEA.card = (H.induce A).ordNonEdges := Finset.card_map _
        have hNEBC_c : NEBC.card = (H.induce BC).ordNonEdges := Finset.card_map _
        have hM1_c : M1.card = H.twoPathMid v := rfl
        have hM2_c : M2.card = H.twoPathMid v := Finset.card_map _
        have hNE_c : NE.card = H.ordNonEdges := rfl
        linarith
      -- Combined topological rank: A in [0, M-1], v at M, BC in [M+1, ...]
      let univA : Finset {z : V // z ∈ A} := Finset.univ
      let M : ℕ := (univA.image r₁).sup id + 1
      have hr₁_lt_M : ∀ a : {z : V // z ∈ A}, r₁ a < M := by
        intro a
        have ha_mem : a ∈ univA := Finset.mem_univ a
        have hle : r₁ a ≤ (univA.image r₁).sup id :=
          Finset.le_sup (f := id) (Finset.mem_image_of_mem r₁ ha_mem)
        exact Nat.lt_succ_of_le hle
      let rank : V → ℕ := fun x =>
        if hxA : x ∈ A then r₁ ⟨x, hxA⟩
        else if hxv : x = v then M
        else r₂ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩, hxA⟩⟩ + M + 1
      have hrank_inj : Function.Injective rank := by
        intro x y hxy
        by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
        · simp only [rank, hxA, hyA, ↓reduceDIte] at hxy
          exact congrArg Subtype.val (hr₁_inj hxy)
        · exfalso
          have hx_lt := hr₁_lt_M ⟨x, hxA⟩
          by_cases hyv : y = v
          · simp only [rank, hxA, hyv, hv_not_A, ↓reduceDIte] at hxy; omega
          · simp only [rank, hxA, hyA, hyv, ↓reduceDIte] at hxy; omega
        · exfalso
          have hy_lt := hr₁_lt_M ⟨y, hyA⟩
          by_cases hxv : x = v
          · simp only [rank, hyA, hxv, hv_not_A, ↓reduceDIte] at hxy; omega
          · simp only [rank, hxA, hyA, hxv, ↓reduceDIte] at hxy; omega
        · by_cases hxv : x = v <;> by_cases hyv : y = v
          · rw [hxv, hyv]
          · exfalso
            simp only [rank, hyA, hxv, hyv, hv_not_A, ↓reduceDIte] at hxy
            omega
          · exfalso
            simp only [rank, hxA, hxv, hyv, hv_not_A, ↓reduceDIte] at hxy
            omega
          · have hxBC : x ∈ BC := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩, hxA⟩
            have hyBC : y ∈ BC := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ y⟩, hyA⟩
            simp only [rank, hxA, hyA, hxv, hyv, ↓reduceDIte] at hxy
            have hr2_eq : r₂ ⟨x, hxBC⟩ = r₂ ⟨y, hyBC⟩ := by omega
            exact congrArg Subtype.val (hr₂_inj hr2_eq)
      have hrank_dag : ∀ u w : V, H.adj u w → (u, w) ∉ F → rank w < rank u := by
        intro u w huw hnotF
        have hnotF₁ : ∀ huA hwA, (⟨u, huA⟩, ⟨w, hwA⟩) ∉ F₁ := by
          intro huA hwA hmem
          apply hnotF
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_map.mpr ⟨(⟨u, huA⟩, ⟨w, hwA⟩), hmem, rfl⟩))
        have hnotF₂ : ∀ huBC hwBC, (⟨u, huBC⟩, ⟨w, hwBC⟩) ∉ F₂ := by
          intro huBC hwBC hmem
          apply hnotF
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_map.mpr ⟨(⟨u, huBC⟩, ⟨w, hwBC⟩), hmem, rfl⟩))
        by_cases huA : u ∈ A
        · by_cases hwA : w ∈ A
          · simp only [rank, huA, hwA, ↓reduceDIte]
            exact hr₁_dag ⟨u, huA⟩ ⟨w, hwA⟩ huw (hnotF₁ huA hwA)
          · exfalso
            have hv_u : H.adj v u := (Digraph.mem_outSet H.toDigraph).mp huA
            by_cases hwv : w = v
            · rw [hwv] at huw; exact H.asymm v u hv_u huw
            · by_cases hw_in : H.adj w v
              · exact hH ⟨v, u, w, hv_u, huw, hw_in⟩
              · have hn_vw : ¬ H.adj v w := fun hvw => hwA ((Digraph.mem_outSet H.toDigraph).mpr hvw)
                have hmemEAC : (u, w) ∈ EAC := by
                  simp only [EAC, C, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
                  exact ⟨⟨huA, hwv, hn_vw, hw_in⟩, huw⟩
                exact hnotF (Finset.mem_union_right _ hmemEAC)
        · by_cases huv : u = v
          · rw [huv] at huw
            have hwA : w ∈ A := (Digraph.mem_outSet H.toDigraph).mpr huw
            have hw_lt := hr₁_lt_M ⟨w, hwA⟩
            simp only [rank, huv, hv_not_A, hwA, ↓reduceDIte]
            exact hw_lt
          · have huBC : u ∈ BC := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩, huA⟩
            by_cases hwA : w ∈ A
            · have hw_lt := hr₁_lt_M ⟨w, hwA⟩
              simp only [rank, huA, huv, hwA, ↓reduceDIte]
              omega
            · by_cases hwv : w = v
              · simp only [rank, huA, huv, hwv, hv_not_A, ↓reduceDIte]
                omega
              · have hwBC : w ∈ BC := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩, hwA⟩
                simp only [rank, huA, huv, hwA, hwv, ↓reduceDIte]
                have hlt2 := hr₂_dag ⟨u, huBC⟩ ⟨w, hwBC⟩ huw (hnotF₂ huBC hwBC)
                omega
      refine ⟨F, rank, hrank_inj, hrank_dag, ?_⟩
      linarith
    · rw [not_nonempty_iff] at hne
      refine ⟨∅, isEmptyElim, fun x => isEmptyElim x, fun x => isEmptyElim x, ?_⟩
      simp

/-- **HHK + CSS Out-Degree-Squared Theorem (`α_CSS = 1`)**:
In ANY finite nonempty `C₃`-free oriented graph `H` where every vertex has out-degree `≥ d`,
`d * (d + 1) ≤ H.ordNonEdges` (hence `d^2 ≤ 2 * γ(H)`). -/
theorem outDeg_sq_le_ordNonEdges {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : OrientedGraph V) [DecidableRel H.adj] (hH : H.TriangleFree)
    {d : ℕ} (hdeg : ∀ u : V, d ≤ H.toDigraph.outDeg u) :
    d * (d + 1) ≤ H.ordNonEdges := by
  obtain ⟨F, rank, hinj, hdag, hcard⟩ := H.exists_feedback_two_card_le_ordNonEdges hH
  exact le_trans (deg_sq_le_two_card_feedback d H F rank hinj hdag hdeg) hcard

/-- Every finite nonempty `C₃`-free oriented graph `H` has a vertex `w` satisfying
`outDeg H w * (outDeg H w + 1) ≤ H.ordNonEdges`. -/
theorem exists_outDeg_sq_le_ordNonEdges {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : OrientedGraph V) [DecidableRel H.adj] (hH : H.TriangleFree) :
    ∃ w : V, H.toDigraph.outDeg w * (H.toDigraph.outDeg w + 1) ≤ H.ordNonEdges := by
  obtain ⟨w, _, hw_min⟩ :=
    Finset.exists_min_image Finset.univ (H.toDigraph.outDeg) Finset.univ_nonempty
  refine ⟨w, H.outDeg_sq_le_ordNonEdges hH (fun u => hw_min u (Finset.mem_univ u))⟩

end OrientedGraph

end CaccettaHaggkvist
