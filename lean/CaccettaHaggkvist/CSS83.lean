module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical
public import CaccettaHaggkvist.CSS
public import CaccettaHaggkvist.CSS56

/-!
# Feedback arc sets with coefficient `83/100`

For a finite loopless digraph with no directed cycle of length two or three,
200 times the size of the feedback set is at most 83 times the number of ordered nonedges. Each unordered nonedge contributes two ordered nonedges.
The construction also gives an injective topological ranking after the feedback arcs are removed.
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

/-! ## Section 1: Pure Real Algebraic Lemmas (Zero `√`, Tiny Denominators) -/

private lemma step3_u_algebra_83 {m s c : ℝ} (hc : 0 < c) (_hm : 0 ≤ m)
    (hms : m ≤ s) (h32 : 2 * s ≤ 3 * m) :
    (100 / 83 : ℝ) * ((m + s) / (2 * c)) ≤ (12 / 25 : ℝ) * (m * s / (c ^ 2)) + 197 / 250 := by
  let y : ℝ := (m + s) / (2 * c)
  have hprod : 0 ≤ (3 * m - 2 * s) * (3 * s - 2 * m) :=
    mul_nonneg (by linarith) (by linarith)
  have h24 : 6 * (m + s) ^ 2 ≤ 25 * (m * s) := by linarith
  have hy_sq : 24 * y ^ 2 ≤ 25 * (m * s / (c ^ 2)) := by
    dsimp [y]
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    rw [div_pow, mul_pow]
    calc 24 * ((m + s) ^ 2 / (2 ^ 2 * c ^ 2))
        = (6 * (m + s) ^ 2) / (c ^ 2) := by ring
      _ ≤ (25 * (m * s)) / (c ^ 2) := div_le_div_of_nonneg_right h24 hc2.le
      _ = 25 * (m * s / (c ^ 2)) := by ring
  have hsq : 0 ≤ (11952 * y - 15625) ^ 2 := sq_nonneg _
  dsimp [y] at hy_sq hsq
  linarith

private lemma step3_w0_algebra_83 {m s c : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (h32 : 3 * m ≤ 2 * s) :
    (100 / 83 : ℝ) * (m / c) ≤ (12 / 25 : ℝ) * (m * s / (c ^ 2)) + 101 / 200 := by
  let z : ℝ := m / c
  have hms : 3 * m ^ 2 ≤ 2 * (m * s) := by nlinarith
  have hz_sq : 3 * z ^ 2 ≤ 2 * (m * s / (c ^ 2)) := by
    dsimp [z]
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    rw [div_pow]
    calc 3 * (m ^ 2 / c ^ 2) = (3 * m ^ 2) / (c ^ 2) := by ring
      _ ≤ (2 * (m * s)) / (c ^ 2) := div_le_div_of_nonneg_right hms hc2.le
      _ = 2 * (m * s / (c ^ 2)) := by ring
  have hsq : 0 ≤ (747 * z - 625) ^ 2 := sq_nonneg _
  dsimp [z] at hz_sq hsq
  linarith

private lemma step3_w1_algebra_83 {m s c : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (h32 : 3 * m ≤ 2 * s) :
    (100 / 83 : ℝ) * (m / c) - (s - m) / c ≤ (12 / 25 : ℝ) * (m * s / (c ^ 2)) + 7 / 40 := by
  let z : ℝ := m / c
  have hms : 3 * m ^ 2 ≤ 2 * (m * s) := by nlinarith
  have hz_sq : 3 * z ^ 2 ≤ 2 * (m * s / (c ^ 2)) := by
    dsimp [z]
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    rw [div_pow]
    calc 3 * (m ^ 2 / c ^ 2) = (3 * m ^ 2) / (c ^ 2) := by ring
      _ ≤ (2 * (m * s)) / (c ^ 2) := div_le_div_of_nonneg_right hms hc2.le
      _ = 2 * (m * s / (c ^ 2)) := by ring
  have hsm : z / 2 ≤ (s - m) / c := by
    dsimp [z]
    rw [div_div]
    have h1 : m ≤ 2 * (s - m) := by linarith
    calc m / (c * 2) ≤ (2 * (s - m)) / (c * 2) := div_le_div_of_nonneg_right h1 (by positivity)
      _ = (s - m) / c := by ring
  have hsq : 0 ≤ (664 * z - 325) ^ 2 := sq_nonneg _
  dsimp [z] at hz_sq hsm hsq
  linarith

private lemma step4_final_contradiction_83 {g x qW a t₁ t₂ t₃ m₃ : ℝ}
    (hg_gt : 83 / 80 + (1059 / 680) * (t₁ + t₂ + t₃) < g)
    (hstep3 : g - (100 / 83) * x + qW ≥
      (13 / 25) * g - (197 / 250) * a - (101 / 200) * (1 - a) + (33 / 50) * m₃)
    (hcut3 : g - (100 / 83) * x + qW <
      (133 / 166) * t₁ + (183 / 166) * t₂ + (100 / 83) * m₃ - a ^ 2 / 4 - a * (1 - a) / 2)
    (ht1_nn : 0 ≤ t₁)
    (ht2_le : t₂ ≤ a * (1 - a))
    (hm3_nn : 0 ≤ m₃)
    (hm3_t3 : m₃ ≤ t₃) : False := by
  have hsq : 0 ≤ (60089 * a - 53326) ^ 2 := sq_nonneg _
  linarith

private lemma finset_disjoint_filter_neg {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Disjoint (s.filter p) (s.filter fun x => ¬ p x) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

private lemma finset_filter_union_neg {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  by_cases hp : p x <;> simp [hp]

private lemma ite_sum_zero {α : Type*} (P : Prop) [Decidable P] (s : Finset α) (f : α → ℝ) :
    (if P then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if P then f x else 0 := by
  split_ifs <;> simp

private lemma sum_inner_union {α β : Type*} [DecidableEq β]
    (s : Finset α) {t₁ t₂ : Finset β} (ht : Disjoint t₁ t₂) (f : α → β → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t₁ ∪ t₂, f x y) =
      (∑ x ∈ s, ∑ y ∈ t₁, f x y) + (∑ x ∈ s, ∑ y ∈ t₂, f x y) := by
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_union ht, Finset.sum_add_distrib]

private lemma sum_union_sum_union {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} (hs : Disjoint s₁ s₂) (ht : Disjoint t₁ t₂)
    (f : α → β → ℝ) :
    (∑ x ∈ s₁ ∪ s₂, ∑ y ∈ t₁ ∪ t₂, f x y) =
      (∑ x ∈ s₁, ∑ y ∈ t₁, f x y) + (∑ x ∈ s₁, ∑ y ∈ t₂, f x y) +
      (∑ x ∈ s₂, ∑ y ∈ t₁, f x y) + (∑ x ∈ s₂, ∑ y ∈ t₂, f x y) := by
  rw [Finset.sum_union hs, sum_inner_union s₁ ht f, sum_inner_union s₂ ht f]
  ring

/-! ## Section 2: Boolean Cube Involution Identities on `V → Bool` -/

private def flipAt {V : Type u} [DecidableEq V] (u : V) : (V → Bool) ≃ (V → Bool) where
  toFun ω := Function.update ω u (!ω u)
  invFun ω := Function.update ω u (!ω u)
  left_inv ω := by ext x; by_cases hx : x = u <;> simp [hx]
  right_inv ω := by ext x; by_cases hx : x = u <;> simp [hx]

private def omegaCard (V : Type u) [Fintype V] [DecidableEq V] : ℝ :=
  (Fintype.card (V → Bool) : ℝ)

private lemma omegaCard_pos {V : Type u} [Fintype V] [DecidableEq V] : 0 < omegaCard V := by
  have _ : Nonempty (V → Bool) := ⟨fun _ => false⟩
  unfold omegaCard
  exact Nat.cast_pos.mpr (Fintype.card_pos (α := V → Bool))

private lemma sum_bool_eq {V : Type u} [Fintype V] [DecidableEq V] (u : V) (b : Bool) :
    ∑ ω : V → Bool, (if ω u = b then (1 : ℝ) else 0) = omegaCard V / 2 := by
  let S := fun c : Bool => ∑ ω : V → Bool, (if ω u = c then (1 : ℝ) else 0)
  have hflip : S (!b) = S b := by
    dsimp [S]
    rw [← Equiv.sum_comp (flipAt u)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [flipAt, Equiv.coe_fn_mk, Function.update_self]
    cases ω u <;> cases b <;> simp
  have htot : S b + S (!b) = omegaCard V := by
    dsimp [S, omegaCard]
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ ω ∈ (Finset.univ : Finset (V → Bool)),
        (if ω u = b then (1 : ℝ) else 0) + (if ω u = !b then 1 else 0) = 1 := by
      intro ω _
      cases ω u <;> cases b <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  change S b = omegaCard V / 2
  linarith

private lemma sum_bool_pair_eq {V : Type u} [Fintype V] [DecidableEq V]
    {u w : V} (hne : u ≠ w) (b₁ b₂ : Bool) :
    ∑ ω : V → Bool, (if ω u = b₁ ∧ ω w = b₂ then (1 : ℝ) else 0) = omegaCard V / 4 := by
  let J := fun c₁ c₂ : Bool =>
    ∑ ω : V → Bool, (if ω u = c₁ ∧ ω w = c₂ then (1 : ℝ) else 0)
  have hflip_u : ∀ c₁ c₂, J (!c₁) c₂ = J c₁ c₂ := by
    intro c₁ c₂
    dsimp [J]
    rw [← Equiv.sum_comp (flipAt u)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [flipAt, Equiv.coe_fn_mk, Function.update_self, Function.update_of_ne hne.symm]
    cases ω u <;> cases c₁ <;> simp
  have hflip_w : ∀ c₁ c₂, J c₁ (!c₂) = J c₁ c₂ := by
    intro c₁ c₂
    dsimp [J]
    rw [← Equiv.sum_comp (flipAt w)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [flipAt, Equiv.coe_fn_mk, Function.update_self, Function.update_of_ne hne]
    cases ω w <;> cases c₂ <;> simp
  have h1 : J (!b₁) b₂ = J b₁ b₂ := hflip_u b₁ b₂
  have h2 : J b₁ (!b₂) = J b₁ b₂ := hflip_w b₁ b₂
  have h3 : J (!b₁) (!b₂) = J b₁ b₂ := (hflip_u b₁ (!b₂)).trans h2
  have htot : J b₁ b₂ + J (!b₁) b₂ + J b₁ (!b₂) + J (!b₁) (!b₂) = omegaCard V := by
    dsimp [J, omegaCard]
    simp only [← Finset.sum_add_distrib]
    have hall : ∀ ω ∈ (Finset.univ : Finset (V → Bool)),
        (if ω u = b₁ ∧ ω w = b₂ then (1 : ℝ) else 0) +
          (if ω u = !b₁ ∧ ω w = b₂ then 1 else 0) +
          (if ω u = b₁ ∧ ω w = !b₂ then 1 else 0) +
          (if ω u = !b₁ ∧ ω w = !b₂ then 1 else 0) = 1 := by
      intro ω _
      cases ω u <;> cases ω w <;> cases b₁ <;> cases b₂ <;> simp
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  change J b₁ b₂ = omegaCard V / 4
  linarith

private lemma sum_bool_neq_eq {V : Type u} [Fintype V] [DecidableEq V]
    {u w : V} (hne : u ≠ w) :
    ∑ ω : V → Bool, (if ω u ≠ ω w then (1 : ℝ) else 0) = omegaCard V / 2 := by
  have hsplit : ∀ ω ∈ (Finset.univ : Finset (V → Bool)),
      (if ω u ≠ ω w then (1 : ℝ) else 0) =
        (if ω u = true ∧ ω w = false then 1 else 0) +
          (if ω u = false ∧ ω w = true then 1 else 0) := by
    intro ω _
    cases ω u <;> cases ω w <;> simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_bool_pair_eq hne true false, sum_bool_pair_eq hne false true]
  ring

/-! ## Section 3: Digraph Indicator Sums & General Cut Reduction -/

namespace OrientedGraph

section CSS83

private def arcInd {V : Type u} (H : OrientedGraph V) [DecidableRel H.adj] (x y : V) : ℝ :=
  if H.adj x y then 1 else 0

private def nonAdjInd {V : Type u} [DecidableEq V] (H : OrientedGraph V) [DecidableRel H.adj]
    (x y : V) : ℝ :=
  if x ≠ y ∧ ¬ H.adj x y ∧ ¬ H.adj y x then 1 else 0

private lemma arcInd_nonneg {V : Type u} (H : OrientedGraph V) [DecidableRel H.adj] (x y : V) :
    0 ≤ H.arcInd x y := by
  unfold arcInd; split_ifs <;> norm_num

private lemma nonAdjInd_nonneg {V : Type u} [DecidableEq V] (H : OrientedGraph V)
    [DecidableRel H.adj] (x y : V) : 0 ≤ H.nonAdjInd x y := by
  unfold nonAdjInd; split_ifs <;> norm_num

private lemma arcInd_self {V : Type u} (H : OrientedGraph V) [DecidableRel H.adj] (x : V) :
    H.arcInd x x = 0 := by
  simp [arcInd, H.loopless x]

private lemma nonAdjInd_self {V : Type u} [DecidableEq V] (H : OrientedGraph V)
    [DecidableRel H.adj] (x : V) : H.nonAdjInd x x = 0 := by
  simp [nonAdjInd]

private lemma nonAdjInd_symm {V : Type u} [DecidableEq V] (H : OrientedGraph V)
    [DecidableRel H.adj] (x y : V) : H.nonAdjInd x y = H.nonAdjInd y x := by
  unfold nonAdjInd
  by_cases hxy : x = y
  · subst hxy; simp
  · have hyx : y ≠ x := Ne.symm hxy
    by_cases h1 : H.adj x y <;> by_cases h2 : H.adj y x <;> simp [hxy, hyx, h1, h2]

private lemma arc_add_arc_add_nonAdj {V : Type u} [DecidableEq V] (H : OrientedGraph V)
    [DecidableRel H.adj] {x y : V} (hne : x ≠ y) :
    H.arcInd x y + H.arcInd y x + H.nonAdjInd x y = 1 := by
  unfold arcInd nonAdjInd
  by_cases h1 : H.adj x y
  · have h2 : ¬ H.adj y x := H.asymm x y h1
    simp [hne, h1, h2]
  · by_cases h2 : H.adj y x <;> simp [hne, h1, h2]

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (H : OrientedGraph V) [DecidableRel H.adj]

private lemma ordNonEdges_eq_sum :
    (H.ordNonEdges : ℝ) = ∑ x : V, ∑ y : V, H.nonAdjInd x y := by
  unfold ordNonEdges nonAdjInd
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter, Fintype.sum_prod_type]

omit [Fintype V] in
private lemma ordNonEdges_induce_eq_sum (S : Finset V) :
    ((H.induce S).ordNonEdges : ℝ) = ∑ x ∈ S, ∑ y ∈ S, H.nonAdjInd x y := by
  rw [(H.induce S).ordNonEdges_eq_sum]
  rw [← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold nonAdjInd
  simp only [ne_eq, Subtype.ext_iff, induce]

private def ASet (v : V) : Finset V := H.toDigraph.outSet v
private def BSet (v : V) : Finset V := H.toDigraph.inSet v
private def CSet (v : V) : Finset V :=
  Finset.univ.filter fun x => x ≠ v ∧ ¬ H.adj v x ∧ ¬ H.adj x v

omit [DecidableEq V] in
private lemma disjoint_ASet_BSet (v : V) : Disjoint (H.ASet v) (H.BSet v) :=
  H.disjoint_outSet_inSet v

private lemma disjoint_ASet_CSet (v : V) : Disjoint (H.ASet v) (H.CSet v) := by
  rw [Finset.disjoint_left]
  intro x hxA hxC
  exact (Finset.mem_filter.mp hxC).2.2.1 ((Digraph.mem_outSet H.toDigraph).mp hxA)

private lemma disjoint_BSet_CSet (v : V) : Disjoint (H.BSet v) (H.CSet v) := by
  rw [Finset.disjoint_left]
  intro x hxB hxC
  exact (Finset.mem_filter.mp hxC).2.2.2 ((Digraph.mem_inSet H.toDigraph).mp hxB)

private def tauReal (v : V) (side : V → Bool) : ℝ :=
  (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, (if side u = false then 1 else 0) * H.arcInd a u) +
  (∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, (if side u = true then 1 else 0) * H.arcInd u b) +
  (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, (if side u = true ∧ side w = false then 1 else 0) * H.arcInd u w)

private def ordRhoReal (v : V) (side : V → Bool) : ℝ :=
  2 * ((H.CSet v).card : ℝ) +
  2 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) +
  2 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, (if side u = false then 1 else 0) * H.nonAdjInd a u) +
  2 * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, (if side u = true then 1 else 0) * H.nonAdjInd b u) +
  (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, (if side u ≠ side w then 1 else 0) * H.nonAdjInd u w)

private lemma exists_feedback_of_good_cut
    (hH : H.TriangleFree) (v : V) (side : V → Bool)
    (ih : ∀ (S : Finset V), S.card < Fintype.card V →
      ∃ (F : Finset ({z : V // z ∈ S} × {z : V // z ∈ S})) (r : {z : V // z ∈ S} → ℕ),
        Function.Injective r ∧
        (∀ x y, (H.induce S).adj x y → (x, y) ∉ F → r y < r x) ∧
        200 * F.card ≤ 83 * (H.induce S).ordNonEdges)
    (hgood : 200 * H.tauReal v side ≤ 83 * H.ordRhoReal v side) :
    ∃ (F : Finset (V × V)) (rank : V → ℕ),
      Function.Injective rank ∧
      (∀ u w : V, H.adj u w → (u, w) ∉ F → rank w < rank u) ∧
      200 * F.card ≤ 83 * H.ordNonEdges := by
  let CA : Finset V := (H.CSet v).filter fun u => side u = true
  let CB : Finset V := (H.CSet v).filter fun u => side u = false
  let V₂ : Finset V := H.ASet v ∪ CA
  let V₁ : Finset V := H.BSet v ∪ CB
  have hv_not_V₂ : v ∉ V₂ := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hA | hCA
    · exact H.loopless v ((Digraph.mem_outSet H.toDigraph).mp hA)
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hCA).1).2.1 rfl
  have hv_not_V₁ : v ∉ V₁ := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hB | hCB
    · exact H.loopless v ((Digraph.mem_inSet H.toDigraph).mp hB)
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hCB).1).2.1 rfl
  have hV₂_lt : V₂.card < Fintype.card V := by
    calc V₂.card < (insert v V₂).card := by rw [Finset.card_insert_of_notMem hv_not_V₂]; omega
      _ ≤ Fintype.card V := Finset.card_le_univ _
  have hV₁_lt : V₁.card < Fintype.card V := by
    calc V₁.card < (insert v V₁).card := by rw [Finset.card_insert_of_notMem hv_not_V₁]; omega
      _ ≤ Fintype.card V := Finset.card_le_univ _
  obtain ⟨F₁, r₁, hr₁_inj, hr₁_dag, hF₁_card⟩ := ih V₁ hV₁_lt
  obtain ⟨F₂, r₂, hr₂_inj, hr₂_dag, hF₂_card⟩ := ih V₂ hV₂_lt
  have hdisj_A_CA : Disjoint (H.ASet v) CA :=
    (H.disjoint_ASet_CSet v).mono_right (Finset.filter_subset _ _)
  have hdisj_B_CB : Disjoint (H.BSet v) CB :=
    (H.disjoint_BSet_CSet v).mono_right (Finset.filter_subset _ _)
  have hdisj_CA_CB : Disjoint CA CB := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    rw [h1] at h2; cases h2
  have hdisj_V₂_V₁ : Disjoint V₂ V₁ := by
    rw [Finset.disjoint_left]
    intro x hx2 hx1
    rcases Finset.mem_union.mp hx2 with hxA | hxCA <;>
      rcases Finset.mem_union.mp hx1 with hxB | hxCB
    · exact Finset.disjoint_left.mp (H.disjoint_ASet_BSet v) hxA hxB
    · exact Finset.disjoint_left.mp (H.disjoint_ASet_CSet v) hxA (Finset.filter_subset _ _ hxCB)
    · exact Finset.disjoint_left.mp (H.disjoint_BSet_CSet v) hxB (Finset.filter_subset _ _ hxCA)
    · exact Finset.disjoint_left.mp hdisj_CA_CB hxCA hxCB
  let E_cut : Finset (V × V) := (V₂ ×ˢ V₁).filter fun p => H.adj p.1 p.2
  let emb₁ : ({z : V // z ∈ V₁} × {z : V // z ∈ V₁}) ↪ V × V :=
    ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
      rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
      injection h with ha hb; subst ha; subst hb; rfl⟩
  let emb₂ : ({z : V // z ∈ V₂} × {z : V // z ∈ V₂}) ↪ V × V :=
    ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
      rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
      injection h with ha hb; subst ha; subst hb; rfl⟩
  let F : Finset (V × V) := (F₁.map emb₁) ∪ (F₂.map emb₂) ∪ E_cut
  have hF_card_le : (F.card : ℝ) ≤ (F₁.card : ℝ) + (F₂.card : ℝ) + (E_cut.card : ℝ) := by
    have hnat : F.card ≤ F₁.card + F₂.card + E_cut.card := by
      calc F.card ≤ (F₁.map emb₁ ∪ F₂.map emb₂).card + E_cut.card := Finset.card_union_le _ _
        _ ≤ (F₁.map emb₁).card + (F₂.map emb₂).card + E_cut.card :=
            Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ = F₁.card + F₂.card + E_cut.card := by simp
    exact_mod_cast hnat
  have hE_cut_eq : (E_cut.card : ℝ) = H.tauReal v side := by
    have hcard_sum : (E_cut.card : ℝ) = ∑ x ∈ V₂, ∑ y ∈ V₁, H.arcInd x y := by
      dsimp [E_cut]
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one, Finset.sum_filter, Finset.sum_product]
      rfl
    rw [hcard_sum]
    dsimp only [V₂, V₁]
    rw [sum_union_sum_union hdisj_A_CA hdisj_B_CB]
    have hAB_zero : ∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.arcInd a b = 0 := by
      refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
      have hva : H.adj v a := (Digraph.mem_outSet H.toDigraph).mp ha
      have hbv : H.adj b v := (Digraph.mem_inSet H.toDigraph).mp hb
      have hnab : ¬ H.adj a b := fun hab => hH ⟨v, a, b, hva, hab, hbv⟩
      simp [arcInd, hnab]
    have hACB : ∑ a ∈ H.ASet v, ∑ u ∈ CB, H.arcInd a u =
        ∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, (if side u = false then 1 else 0) * H.arcInd a u := by
      refine Finset.sum_congr rfl fun a _ => ?_
      dsimp [CB]; rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
    have hCAB : ∑ u ∈ CA, ∑ b ∈ H.BSet v, H.arcInd u b =
        ∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, (if side u = true then 1 else 0) * H.arcInd u b := by
      dsimp [CA]; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs
      · simp
      · symm; exact Finset.sum_eq_zero fun _ _ => by ring
    have hCACB : ∑ u ∈ CA, ∑ w ∈ CB, H.arcInd u w =
        ∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v,
          (if side u = true ∧ side w = false then 1 else 0) * H.arcInd u w := by
      dsimp [CA, CB]; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      cases hu : side u
      · symm; exact Finset.sum_eq_zero fun _ _ => by simp
      · simp only [true_and, ↓reduceIte]; rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
    rw [hAB_zero, zero_add, hACB, hCAB, hCACB]
    unfold tauReal; ring
  have hNonEdge_le :
      ((H.induce V₁).ordNonEdges : ℝ) + ((H.induce V₂).ordNonEdges : ℝ) +
        H.ordRhoReal v side ≤ (H.ordNonEdges : ℝ) := by
    rw [H.ordNonEdges_eq_sum, H.ordNonEdges_induce_eq_sum V₁, H.ordNonEdges_induce_eq_sum V₂]
    let P₀ : Finset V := {v}
    have hd01 : Disjoint P₀ V₁ := Finset.disjoint_singleton_left.mpr hv_not_V₁
    have hd02 : Disjoint P₀ V₂ := Finset.disjoint_singleton_left.mpr hv_not_V₂
    have hd012 : Disjoint (P₀ ∪ V₁) V₂ :=
      Finset.disjoint_union_left.mpr ⟨hd02, hdisj_V₂_V₁.symm⟩
    let Uall : Finset V := (P₀ ∪ V₁) ∪ V₂
    have hsub_univ : ∑ x ∈ Uall, ∑ y ∈ Uall, H.nonAdjInd x y ≤
        ∑ x : V, ∑ y : V, H.nonAdjInd x y := by
      calc ∑ x ∈ Uall, ∑ y ∈ Uall, H.nonAdjInd x y
          ≤ ∑ x ∈ Uall, ∑ y : V, H.nonAdjInd x y :=
            Finset.sum_le_sum fun x _ =>
              Finset.sum_le_univ_sum_of_nonneg (fun y => H.nonAdjInd_nonneg x y)
        _ ≤ ∑ x : V, ∑ y : V, H.nonAdjInd x y :=
            Finset.sum_le_univ_sum_of_nonneg (fun x =>
              Finset.sum_nonneg fun y _ => H.nonAdjInd_nonneg x y)
    have hexpand : ∑ x ∈ Uall, ∑ y ∈ Uall, H.nonAdjInd x y =
        ((∑ x ∈ V₁, ∑ y ∈ V₁, H.nonAdjInd x y) + (∑ x ∈ V₂, ∑ y ∈ V₂, H.nonAdjInd x y)) +
        (2 * (∑ y ∈ V₁ ∪ V₂, H.nonAdjInd v y) + 2 * (∑ x ∈ V₂, ∑ y ∈ V₁, H.nonAdjInd x y)) := by
      dsimp [Uall]
      rw [sum_union_sum_union hd012 hd012, sum_union_sum_union hd01 hd01,
        Finset.sum_union hd01, sum_inner_union V₂ hd01]
      simp only [P₀, Finset.sum_singleton, H.nonAdjInd_self v]
      have hsym_v1 : ∑ x ∈ V₁, H.nonAdjInd x v = ∑ x ∈ V₁, H.nonAdjInd v x :=
        Finset.sum_congr rfl fun x _ => H.nonAdjInd_symm x v
      have hsym_v2 : ∑ x ∈ V₂, H.nonAdjInd x v = ∑ x ∈ V₂, H.nonAdjInd v x :=
        Finset.sum_congr rfl fun x _ => H.nonAdjInd_symm x v
      have hsym_12 : ∑ x ∈ V₁, ∑ y ∈ V₂, H.nonAdjInd x y =
          ∑ x ∈ V₂, ∑ y ∈ V₁, H.nonAdjInd x y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => H.nonAdjInd_symm y x
      have hv_u : ∑ y ∈ V₁ ∪ V₂, H.nonAdjInd v y =
          (∑ y ∈ V₁, H.nonAdjInd v y) + (∑ y ∈ V₂, H.nonAdjInd v y) :=
        Finset.sum_union hdisj_V₂_V₁.symm
      rw [hsym_v1, hsym_v2, hsym_12, hv_u]; ring
    have hv_C : ∑ y ∈ V₁ ∪ V₂, H.nonAdjInd v y = ((H.CSet v).card : ℝ) := by
      have hunion_eq : V₁ ∪ V₂ = (H.ASet v ∪ H.BSet v) ∪ H.CSet v := by
        ext x
        simp only [V₁, V₂, CA, CB, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ((hxB | ⟨hxC, _⟩) | (hxA | ⟨hxC, _⟩))
          · exact Or.inl (Or.inr hxB)
          · exact Or.inr hxC
          · exact Or.inl (Or.inl hxA)
          · exact Or.inr hxC
        · rintro ((hxA | hxB) | hxC)
          · exact Or.inr (Or.inl hxA)
          · exact Or.inl (Or.inl hxB)
          · cases hside : side x
            · exact Or.inl (Or.inr ⟨hxC, rfl⟩)
            · exact Or.inr (Or.inr ⟨hxC, rfl⟩)
      have hd_ABC : Disjoint (H.ASet v ∪ H.BSet v) (H.CSet v) :=
        Finset.disjoint_union_left.mpr ⟨H.disjoint_ASet_CSet v, H.disjoint_BSet_CSet v⟩
      rw [hunion_eq, Finset.sum_union hd_ABC]
      have hAB0 : ∑ y ∈ H.ASet v ∪ H.BSet v, H.nonAdjInd v y = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        rcases Finset.mem_union.mp hy with hyA | hyB
        · have hvy := (Digraph.mem_outSet H.toDigraph).mp hyA
          simp [nonAdjInd, hvy]
        · have hyv := (Digraph.mem_inSet H.toDigraph).mp hyB
          simp [nonAdjInd, hyv]
      have hC1 : ∑ y ∈ H.CSet v, H.nonAdjInd v y = ((H.CSet v).card : ℝ) := by
        have hall1 : ∀ y ∈ H.CSet v, H.nonAdjInd v y = 1 := by
          intro y hy
          rcases (Finset.mem_filter.mp hy).2 with ⟨hyv, hn1, hn2⟩
          have hvy_ne : v ≠ y := Ne.symm hyv
          simp [nonAdjInd, hvy_ne, hn1, hn2]
        rw [Finset.sum_congr rfl hall1, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hAB0, hC1, zero_add]
    have hcross : 2 * (∑ x ∈ V₂, ∑ y ∈ V₁, H.nonAdjInd x y) =
        H.ordRhoReal v side - 2 * ((H.CSet v).card : ℝ) := by
      dsimp only [V₂, V₁]
      rw [sum_union_sum_union hdisj_A_CA hdisj_B_CB]
      have hACB : ∑ a ∈ H.ASet v, ∑ u ∈ CB, H.nonAdjInd a u =
          ∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, (if side u = false then 1 else 0) * H.nonAdjInd a u := by
        refine Finset.sum_congr rfl fun a _ => ?_
        dsimp [CB]; rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
      have hCAB : ∑ u ∈ CA, ∑ b ∈ H.BSet v, H.nonAdjInd u b =
          ∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, (if side u = true then 1 else 0) * H.nonAdjInd b u := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        dsimp [CA]; rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [H.nonAdjInd_symm u b]
        split_ifs <;> ring
      have hCACB : 2 * (∑ u ∈ CA, ∑ w ∈ CB, H.nonAdjInd u w) =
          ∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, (if side u ≠ side w then 1 else 0) * H.nonAdjInd u w := by
        have h1 : ∑ u ∈ CA, ∑ w ∈ CB, H.nonAdjInd u w =
            ∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v,
              (if side u = true ∧ side w = false then 1 else 0) * H.nonAdjInd u w := by
          dsimp [CA, CB]; rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun u _ => ?_
          cases hu : side u
          · symm; exact Finset.sum_eq_zero fun _ _ => by simp
          · simp only [true_and, ↓reduceIte]; rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
        have h2 : ∑ u ∈ CA, ∑ w ∈ CB, H.nonAdjInd u w =
            ∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v,
              (if side u = false ∧ side w = true then 1 else 0) * H.nonAdjInd u w := by
          rw [h1, Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
          rw [H.nonAdjInd_symm w u]
          cases side u <;> cases side w <;> simp
        have h12 : 2 * (∑ u ∈ CA, ∑ w ∈ CB, H.nonAdjInd u w) =
            (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v,
              (if side u = true ∧ side w = false then 1 else 0) * H.nonAdjInd u w) +
            (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v,
              (if side u = false ∧ side w = true then 1 else 0) * H.nonAdjInd u w) := by
          linarith [h1, h2]
        rw [h12, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        cases side u <;> cases side w <;> simp
      unfold ordRhoReal
      linarith
    linarith [hsub_univ, hexpand, hv_C, hcross]
  let univ₂ : Finset {z : V // z ∈ V₂} := Finset.univ
  let M : ℕ := (univ₂.image r₂).sup id + 1
  have hr₂_lt_M : ∀ a : {z : V // z ∈ V₂}, r₂ a < M := by
    intro a
    have ha_mem : a ∈ univ₂ := Finset.mem_univ a
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_image_of_mem r₂ ha_mem))
  have hmem_V₁_of : ∀ x : V, x ∉ V₂ → x ≠ v → x ∈ V₁ := by
    intro x hx2 hxv
    by_cases hvx : H.adj v x
    · exact (hx2 (Finset.mem_union_left _ ((Digraph.mem_outSet H.toDigraph).mpr hvx))).elim
    · by_cases hxv_adj : H.adj x v
      · exact Finset.mem_union_left _ ((Digraph.mem_inSet H.toDigraph).mpr hxv_adj)
      · have hxC : x ∈ H.CSet v := Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hxv, hvx, hxv_adj⟩⟩
        cases hside : side x
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxC, hside⟩)
        · exact (hx2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxC, hside⟩))).elim
  let rank : V → ℕ := fun x =>
    if hx2 : x ∈ V₂ then r₂ ⟨x, hx2⟩
    else if hxv : x = v then M
    else r₁ ⟨x, hmem_V₁_of x hx2 hxv⟩ + M + 1
  have hrank_inj : Function.Injective rank := by
    intro x y hxy
    by_cases hx2 : x ∈ V₂ <;> by_cases hy2 : y ∈ V₂
    · simp only [rank, hx2, hy2, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (hr₂_inj hxy)
    · exfalso
      have hx_lt := hr₂_lt_M ⟨x, hx2⟩
      by_cases hyv : y = v
      · simp only [rank, hx2, hyv, hv_not_V₂, ↓reduceDIte] at hxy; omega
      · simp only [rank, hx2, hy2, hyv, ↓reduceDIte] at hxy; omega
    · exfalso
      have hy_lt := hr₂_lt_M ⟨y, hy2⟩
      by_cases hxv : x = v
      · simp only [rank, hy2, hxv, hv_not_V₂, ↓reduceDIte] at hxy; omega
      · simp only [rank, hx2, hy2, hxv, ↓reduceDIte] at hxy; omega
    · by_cases hxv : x = v <;> by_cases hyv : y = v
      · rw [hxv, hyv]
      · exfalso; simp only [rank, hy2, hxv, hyv, hv_not_V₂, ↓reduceDIte] at hxy; omega
      · exfalso; simp only [rank, hx2, hxv, hyv, hv_not_V₂, ↓reduceDIte] at hxy; omega
      · have hx1 := hmem_V₁_of x hx2 hxv
        have hy1 := hmem_V₁_of y hy2 hyv
        simp only [rank, hx2, hy2, hxv, hyv, ↓reduceDIte] at hxy
        have hr1_eq : r₁ ⟨x, hx1⟩ = r₁ ⟨y, hy1⟩ := by omega
        exact congrArg Subtype.val (hr₁_inj hr1_eq)
  have hrank_dag : ∀ u w : V, H.adj u w → (u, w) ∉ F → rank w < rank u := by
    intro u w huw hnotF
    have hnotF₁ : ∀ hu1 hw1, (⟨u, hu1⟩, ⟨w, hw1⟩) ∉ F₁ := fun hu1 hw1 hm =>
      hnotF (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨_, hm, rfl⟩)))
    have hnotF₂ : ∀ hu2 hw2, (⟨u, hu2⟩, ⟨w, hw2⟩) ∉ F₂ := fun hu2 hw2 hm =>
      hnotF (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_, hm, rfl⟩)))
    by_cases hu2 : u ∈ V₂
    · by_cases hw2 : w ∈ V₂
      · simp only [rank, hu2, hw2, ↓reduceDIte]
        exact hr₂_dag ⟨u, hu2⟩ ⟨w, hw2⟩ huw (hnotF₂ hu2 hw2)
      · exfalso
        by_cases hwv : w = v
        · rw [hwv] at huw
          rcases Finset.mem_union.mp hu2 with huA | huCA
          · exact H.asymm v u ((Digraph.mem_outSet H.toDigraph).mp huA) huw
          · exact (Finset.mem_filter.mp (Finset.mem_filter.mp huCA).1).2.2.2 huw
        · have hw1 := hmem_V₁_of w hw2 hwv
          have hmemE : (u, w) ∈ E_cut :=
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu2, hw1⟩, huw⟩
          exact hnotF (Finset.mem_union_right _ hmemE)
    · by_cases huv : u = v
      · rw [huv] at huw
        have hw2 : w ∈ V₂ := Finset.mem_union_left _ ((Digraph.mem_outSet H.toDigraph).mpr huw)
        have hw_lt := hr₂_lt_M ⟨w, hw2⟩
        simp only [rank, huv, hv_not_V₂, hw2, ↓reduceDIte]
        exact hw_lt
      · have hu1 := hmem_V₁_of u hu2 huv
        by_cases hw2 : w ∈ V₂
        · have hw_lt := hr₂_lt_M ⟨w, hw2⟩
          simp only [rank, hu2, huv, hw2, ↓reduceDIte]; omega
        · by_cases hwv : w = v
          · simp only [rank, hu2, huv, hwv, hv_not_V₂, ↓reduceDIte]; omega
          · have hw1 := hmem_V₁_of w hw2 hwv
            simp only [rank, hu2, huv, hw2, hwv, ↓reduceDIte]
            have hlt1 := hr₁_dag ⟨u, hu1⟩ ⟨w, hw1⟩ huw (hnotF₁ hu1 hw1)
            omega
  have hcard_real : 200 * (F.card : ℝ) ≤ 83 * (H.ordNonEdges : ℝ) := by
    have h1 : 200 * (F₁.card : ℝ) ≤ 83 * ((H.induce V₁).ordNonEdges : ℝ) := by exact_mod_cast hF₁_card
    have h2 : 200 * (F₂.card : ℝ) ≤ 83 * ((H.induce V₂).ordNonEdges : ℝ) := by exact_mod_cast hF₂_card
    linarith [hF_card_le, hE_cut_eq, hgood, hNonEdge_le]
  refine ⟨F, rank, hrank_inj, hrank_dag, ?_⟩
  exact_mod_cast hcard_real

/-! ## Section 4: Step 1 Triple-Counting Identities & Pivot Vertex Selection -/

private lemma triple_sum_eAC_eq_g (hH : H.TriangleFree) :
    ∑ v : V, ∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.arcInd a u =
      ∑ v : V, ∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b := by
  simp only [ASet, BSet, CSet, Digraph.outSet, Digraph.inSet, Finset.sum_filter, ite_sum_zero]
  conv_rhs =>
    arg 2; ext v
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  unfold arcInd nonAdjInd
  by_cases hxy : H.adj x y <;> by_cases hyz : H.adj y z
  · have hzx : ¬ H.adj z x := fun h => hH ⟨x, y, z, hxy, hyz, h⟩
    by_cases hxz : H.adj x z
    · simp [hxy, hyz, hxz]
    · have hnez : z ≠ x := fun h => H.asymm x y hxy (h ▸ hyz)
      simp [hxy, hyz, hxz, hzx, hnez]
  · simp [hxy, hyz]
  · simp [hxy, hyz]
  · simp [hxy, hyz]

private lemma triple_sum_eCB_eq_g (hH : H.TriangleFree) :
    ∑ v : V, ∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, H.arcInd u b =
      ∑ v : V, ∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b := by
  simp only [ASet, BSet, CSet, Digraph.outSet, Digraph.inSet, Finset.sum_filter, ite_sum_zero]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext u
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2; ext v
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  unfold arcInd nonAdjInd
  by_cases hxy : H.adj x y <;> by_cases hyz : H.adj y z
  · have hzx : ¬ H.adj z x := fun h => hH ⟨x, y, z, hxy, hyz, h⟩
    by_cases hxz : H.adj x z
    · simp [hxy, hyz, hxz]
    · have hnez : x ≠ z := fun h => by subst h; exact H.asymm x y hxy hyz
      simp [hxy, hyz, hxz, hzx, hnez, hnez.symm]
  · simp [hyz]
  · simp [hxy, hyz]
  · simp [hyz]

private lemma triple_sum_eBarAC_eq_t :
    ∑ v : V, ∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.nonAdjInd a u =
      ∑ v : V, ∑ x ∈ H.CSet v, ∑ y ∈ H.CSet v, H.arcInd x y := by
  simp only [ASet, CSet, Digraph.outSet, Finset.sum_filter, ite_sum_zero]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2; ext x
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  unfold arcInd nonAdjInd
  by_cases hxy : H.adj x y
  · by_cases hzx_eq : z = x
    · subst hzx_eq; simp [hxy]
    · by_cases hzy_eq : z = y
      · subst hzy_eq; simp [hxy]
      · have hxz_ne : x ≠ z := Ne.symm hzx_eq
        have hyz_ne : y ≠ z := Ne.symm hzy_eq
        by_cases h1 : H.adj x z <;> by_cases h2 : H.adj z x <;>
          by_cases h3 : H.adj y z <;> by_cases h4 : H.adj z y <;>
          simp [hxy, hzx_eq, hxz_ne, hyz_ne, h1, h2, h3, h4]
  · simp [hxy]

private lemma triple_sum_eBarBC_eq_t :
    ∑ v : V, ∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, H.nonAdjInd b u =
      ∑ v : V, ∑ x ∈ H.CSet v, ∑ y ∈ H.CSet v, H.arcInd x y := by
  simp only [BSet, CSet, Digraph.inSet, Finset.sum_filter, ite_sum_zero]
  rw [Finset.sum_comm]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2; ext x
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  unfold arcInd nonAdjInd
  by_cases hxy : H.adj x y
  · by_cases hzx_eq : z = x
    · subst hzx_eq; simp [hxy]
    · by_cases hzy_eq : z = y
      · subst hzy_eq; simp [hxy]
      · have hxz_ne : x ≠ z := Ne.symm hzx_eq
        have hyz_ne : y ≠ z := Ne.symm hzy_eq
        by_cases h1 : H.adj x z <;> by_cases h2 : H.adj z x <;>
          by_cases h3 : H.adj y z <;> by_cases h4 : H.adj z y <;>
          simp [hxy, hzy_eq, hxz_ne, hyz_ne, h1, h2, h3, h4]
  · simp [hxy]

private lemma sum_CSet_nonAdj_eq (v : V) :
    ∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.nonAdjInd u w =
      ((H.CSet v).card : ℝ) * (((H.CSet v).card : ℝ) - 1) -
        2 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) := by
  let C := H.CSet v
  have htot : ∑ u ∈ C, ∑ w ∈ C, (if u ≠ w then (1 : ℝ) else 0) =
      (C.card : ℝ) * ((C.card : ℝ) - 1) := by
    have hinner : ∀ u ∈ C, ∑ w ∈ C, (if u ≠ w then (1 : ℝ) else 0) = (C.card : ℝ) - 1 := by
      intro u hu
      have h1 : ∑ w ∈ C, ((if u ≠ w then (1 : ℝ) else 0) + (if u = w then 1 else 0)) = (C.card : ℝ) := by
        have hall : ∀ w ∈ C, (if u ≠ w then (1 : ℝ) else 0) + (if u = w then 1 else 0) = 1 := by
          intro w _; by_cases h : u = w <;> simp [h]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : ∑ w ∈ C, (if u = w then (1 : ℝ) else 0) = 1 := by
        rw [← Finset.sum_filter]
        have hf : C.filter (fun w => u = w) = {u} := by
          ext w; simp only [Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun ⟨_, hw⟩ => hw.symm, fun hw => ⟨hw ▸ hu, hw.symm⟩⟩
        rw [hf, Finset.sum_singleton]
      rw [Finset.sum_add_distrib, h2] at h1
      linarith
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  have hpart : ∑ u ∈ C, ∑ w ∈ C, (if u ≠ w then (1 : ℝ) else 0) =
      (∑ u ∈ C, ∑ w ∈ C, H.arcInd u w) + (∑ u ∈ C, ∑ w ∈ C, H.arcInd w u) +
        (∑ u ∈ C, ∑ w ∈ C, H.nonAdjInd u w) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    by_cases hne : u = w
    · subst hne; simp [H.arcInd_self u, H.nonAdjInd_self u]
    · simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact (H.arc_add_arc_add_nonAdj hne).symm
  have hcomm : ∑ u ∈ C, ∑ w ∈ C, H.arcInd w u = ∑ u ∈ C, ∑ w ∈ C, H.arcInd u w := Finset.sum_comm
  linarith


private lemma exists_pivot_vertex_83 [Nonempty V] (hH : H.TriangleFree)
    (hbad : ∀ (v : V) (side : V → Bool), 83 * H.ordRhoReal v side < 200 * H.tauReal v side) :
    ∃ v : V, 1 ≤ (H.CSet v).card ∧
      (83 / 80 : ℝ) * ((H.CSet v).card : ℝ) ^ 2 +
        (1059 / 680 : ℝ) * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) <
      (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) := by
  let K : ℝ := omegaCard V
  have hK_pos : 0 < K := omegaCard_pos
  have h_omega_eval : ∀ v : V,
      ∑ ω : V → Bool, (83 * H.ordRhoReal v ω - 200 * H.tauReal v ω) =
      K * (166 * ((H.CSet v).card : ℝ) +
        (83 / 2 : ℝ) * (((H.CSet v).card : ℝ) * (((H.CSet v).card : ℝ) - 1) -
          2 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w)) +
        166 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) +
        83 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.nonAdjInd a u) +
        83 * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, H.nonAdjInd b u) -
        100 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.arcInd a u) -
        100 * (∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, H.arcInd u b) -
        50 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w)) := by
    intro v
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold ordRhoReal tauReal
    simp only [Finset.sum_add_distrib]
    have hc1' : ∑ _ω : V → Bool, (2 * ((H.CSet v).card : ℝ)) = 2 * K * ((H.CSet v).card : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [K, omegaCard]; ring
    have hc2' : ∑ _ω : V → Bool, (2 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) =
        2 * K * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [K, omegaCard]; ring
    have hs_f1 : ∀ (S : Finset V) (F : V → V → ℝ),
        ∑ ω : V → Bool, (∑ a ∈ S, ∑ u ∈ H.CSet v, (if ω u = false then 1 else 0) * F a u) =
        (K / 2) * (∑ a ∈ S, ∑ u ∈ H.CSet v, F a u) := by
      intro S F
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, sum_bool_eq u false]
    have hs_t1 : ∑ ω : V → Bool,
        (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, (if ω u = true then 1 else 0) * H.nonAdjInd b u) =
        (K / 2) * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, H.nonAdjInd b u) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, sum_bool_eq u true]
    have hs_t2 : ∑ ω : V → Bool,
        (∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, (if ω u = true then 1 else 0) * H.arcInd u b) =
        (K / 2) * (∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, H.arcInd u b) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, sum_bool_eq u true]
    have hs_neq : ∑ ω : V → Bool,
        (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, (if ω u ≠ ω w then 1 else 0) * H.nonAdjInd u w) =
        (K / 2) * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.nonAdjInd u w) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hne : u = w
      · subst hne; simp [H.nonAdjInd_self u]
      · rw [← Finset.sum_mul, sum_bool_neq_eq hne]
    have hs_tf : ∑ ω : V → Bool,
        (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, (if ω u = true ∧ ω w = false then 1 else 0) * H.arcInd u w) =
        (K / 4) * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hne : u = w
      · subst hne; simp [H.arcInd_self u]
      · rw [← Finset.sum_mul, sum_bool_pair_eq hne true false]
    have hf_na : ∑ ω : V → Bool,
        (2 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, (if ω u = false then 1 else 0) * H.nonAdjInd a u)) =
        K * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.nonAdjInd a u) := by
      rw [← Finset.mul_sum, hs_f1]; ring
    have ht_nb : ∑ ω : V → Bool,
        (2 * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, (if ω u = true then 1 else 0) * H.nonAdjInd b u)) =
        K * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, H.nonAdjInd b u) := by
      rw [← Finset.mul_sum, hs_t1]; ring
    rw [hc1', hc2', hf_na, ht_nb, hs_neq, hs_f1 (H.ASet v) H.arcInd, hs_t2, hs_tf,
      H.sum_CSet_nonAdj_eq v]
    ring
  have hsum_unif_neg : ∑ v : V,
      (166 * ((H.CSet v).card : ℝ) +
        (83 / 2 : ℝ) * (((H.CSet v).card : ℝ) * (((H.CSet v).card : ℝ) - 1)) +
        33 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) -
        34 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) < 0 := by
    have _ : Nonempty (V → Bool) := ⟨fun _ => false⟩
    have htotal_neg : ∑ v : V,
        (∑ ω : V → Bool, (83 * H.ordRhoReal v ω - 200 * H.tauReal v ω)) < 0 := by
      have hlt_each : ∀ v ∈ (Finset.univ : Finset V),
          ∑ ω : V → Bool, (83 * H.ordRhoReal v ω - 200 * H.tauReal v ω) < 0 := by
        intro v _
        have hlt_ω : ∀ ω ∈ (Finset.univ : Finset (V → Bool)),
            83 * H.ordRhoReal v ω - 200 * H.tauReal v ω < 0 :=
          fun ω _ => sub_neg.mpr (hbad v ω)
        calc ∑ ω : V → Bool, (83 * H.ordRhoReal v ω - 200 * H.tauReal v ω)
            < ∑ _ω : V → Bool, (0 : ℝ) := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt_ω
          _ = 0 := by simp
      calc ∑ v : V, (∑ ω : V → Bool, (83 * H.ordRhoReal v ω - 200 * H.tauReal v ω))
          < ∑ _v : V, (0 : ℝ) := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt_each
        _ = 0 := by simp
    simp_rw [h_omega_eval, ← Finset.mul_sum] at htotal_neg
    have hinner_neg : ∑ v : V, (166 * ((H.CSet v).card : ℝ) +
        (83 / 2 : ℝ) * (((H.CSet v).card : ℝ) * (((H.CSet v).card : ℝ) - 1) -
          2 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w)) +
        166 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) +
        83 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.nonAdjInd a u) +
        83 * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, H.nonAdjInd b u) -
        100 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.arcInd a u) -
        100 * (∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, H.arcInd u b) -
        50 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w)) < 0 := by nlinarith
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hinner_neg ⊢
    rw [H.triple_sum_eAC_eq_g hH, H.triple_sum_eCB_eq_g hH,
      H.triple_sum_eBarAC_eq_t, H.triple_sum_eBarBC_eq_t] at hinner_neg
    linarith
  have hsum_triv_neg : ∑ v : V,
      (332 * ((H.CSet v).card : ℝ) +
        332 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) -
        68 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) < 0 := by
    have hpt_triv : ∀ v : V,
        (83 * H.ordRhoReal v (fun _ => false) - 200 * H.tauReal v (fun _ => false)) +
        (83 * H.ordRhoReal v (fun _ => true) - 200 * H.tauReal v (fun _ => true)) =
        332 * ((H.CSet v).card : ℝ) +
        332 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) +
        166 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.nonAdjInd a u) +
        166 * (∑ b ∈ H.BSet v, ∑ u ∈ H.CSet v, H.nonAdjInd b u) -
        200 * (∑ a ∈ H.ASet v, ∑ u ∈ H.CSet v, H.arcInd a u) -
        200 * (∑ u ∈ H.CSet v, ∑ b ∈ H.BSet v, H.arcInd u b) := by
      intro v
      unfold ordRhoReal tauReal
      simp only [↓reduceIte, one_mul, zero_mul, Bool.false_eq_true, Bool.true_eq_false,
        ne_eq, not_true_eq_false, and_false, false_and, Finset.sum_const_zero]
      ring
    have hlt_each : ∀ v ∈ (Finset.univ : Finset V),
        (83 * H.ordRhoReal v (fun _ => false) - 200 * H.tauReal v (fun _ => false)) +
        (83 * H.ordRhoReal v (fun _ => true) - 200 * H.tauReal v (fun _ => true)) < 0 := by
      intro v _
      have h1 := hbad v (fun _ => false)
      have h2 := hbad v (fun _ => true)
      linarith
    have htot := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt_each
    simp only [Finset.sum_const_zero] at htot
    simp_rw [hpt_triv] at htot
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at htot ⊢
    rw [H.triple_sum_eAC_eq_g hH, H.triple_sum_eCB_eq_g hH,
      H.triple_sum_eBarAC_eq_t, H.triple_sum_eBarBC_eq_t] at htot
    linarith
  have hsum_comb : ∑ v : V,
      (34 * (166 * ((H.CSet v).card : ℝ) +
          (83 / 2 : ℝ) * (((H.CSet v).card : ℝ) * (((H.CSet v).card : ℝ) - 1)) +
          33 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) -
          34 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) +
       3 * (332 * ((H.CSet v).card : ℝ) +
          332 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) -
          68 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b))) < 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith
  have hex_v : ∃ v : V,
      34 * (166 * ((H.CSet v).card : ℝ) +
          (83 / 2 : ℝ) * (((H.CSet v).card : ℝ) * (((H.CSet v).card : ℝ) - 1)) +
          33 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) -
          34 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) +
      3 * (332 * ((H.CSet v).card : ℝ) +
          332 * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) -
          68 * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) < 0 := by
    by_contra hno
    push Not at hno
    have hnn : (0 : ℝ) ≤ ∑ v : V, _ := Finset.sum_nonneg (s := Finset.univ) fun v _ => hno v
    linarith
  obtain ⟨v, hv_neg⟩ := hex_v
  have hc_ge_one : 1 ≤ (H.CSet v).card := by
    by_contra hc0
    have hcard0 : (H.CSet v).card = 0 := by omega
    have hC_emp : H.CSet v = ∅ := Finset.card_eq_zero.mp hcard0
    have hbad0 := hbad v (fun _ => false)
    unfold ordRhoReal tauReal at hbad0
    rw [hC_emp] at hbad0 hv_neg
    simp only [Finset.card_empty, Nat.cast_zero, Finset.sum_empty, Finset.sum_const_zero] at hbad0 hv_neg
    linarith
  refine ⟨v, hc_ge_one, ?_⟩
  have hc_real : (1 : ℝ) ≤ ((H.CSet v).card : ℝ) := by exact_mod_cast hc_ge_one
  nlinarith

/-! ## Section 5: Steps 2–4 Modular Pivot Lemmas & Main Theorem -/

private lemma step2_kl_sum_le (hH : H.TriangleFree) (v : V) :
    ∑ u ∈ H.CSet v,
      (∑ a ∈ H.ASet v, H.arcInd a u) * (∑ b ∈ H.BSet v, H.arcInd u b) ≤
    ((H.CSet v).card : ℝ) * (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b) := by
  have hexp : ∀ u ∈ H.CSet v,
      (∑ a ∈ H.ASet v, H.arcInd a u) * (∑ b ∈ H.BSet v, H.arcInd u b) =
        ∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.arcInd a u * H.arcInd u b := by
    intro u _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have hpt : ∀ u ∈ H.CSet v, H.arcInd a u * H.arcInd u b ≤ H.nonAdjInd a b := by
    intro u _
    have hva : H.adj v a := (Digraph.mem_outSet H.toDigraph).mp ha
    have hbv : H.adj b v := (Digraph.mem_inSet H.toDigraph).mp hb
    unfold arcInd nonAdjInd
    by_cases hau : H.adj a u <;> by_cases hub : H.adj u b
    · have hab_ne : a ≠ b := fun h => by subst h; exact H.asymm v a hva hbv
      have hnab : ¬ H.adj a b := fun hab => hH ⟨v, a, b, hva, hab, hbv⟩
      have hnba : ¬ H.adj b a := fun hba => hH ⟨a, u, b, hau, hub, hba⟩
      simp [hau, hub, hab_ne, hnab, hnba]
    · simp [hau, hub]; split_ifs <;> norm_num
    · simp [hau, hub]; split_ifs <;> norm_num
    · simp [hau, hub]; split_ifs <;> norm_num
  calc ∑ u ∈ H.CSet v, H.arcInd a u * H.arcInd u b
      ≤ ∑ _u ∈ H.CSet v, H.nonAdjInd a b := Finset.sum_le_sum hpt
    _ = ((H.CSet v).card : ℝ) * H.nonAdjInd a b := by
        rw [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq V] in
private def kFn (v u : V) : ℕ := ((H.ASet v).filter fun a => H.adj a u).card
omit [DecidableEq V] in
private def lFn (v u : V) : ℕ := ((H.BSet v).filter fun b => H.adj u b).card
omit [DecidableEq V] in
private def mFn (v u : V) : ℕ := min (H.kFn v u) (H.lFn v u)
omit [DecidableEq V] in
private def sFn (v u : V) : ℕ := max (H.kFn v u) (H.lFn v u)

private def USet (v : V) : Finset V := (H.CSet v).filter fun u => 2 * H.sFn v u ≤ 3 * H.mFn v u
private def WSet (v : V) : Finset V := (H.CSet v).filter fun u => ¬ (2 * H.sFn v u ≤ 3 * H.mFn v u)
private def WASet (v : V) : Finset V := (H.WSet v).filter fun w => H.lFn v w ≤ H.kFn v w
private def WBSet (v : V) : Finset V := (H.WSet v).filter fun w => ¬ (H.lFn v w ≤ H.kFn v w)

private def cCard (v : V) : ℝ := ((H.CSet v).card : ℝ)
private def gRaw (v : V) : ℝ := ∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b
private noncomputable def gNorm (v : V) : ℝ := H.gRaw v / (H.cCard v ^ 2)
private noncomputable def aNorm (v : V) : ℝ := ((H.USet v).card : ℝ) / H.cCard v
private noncomputable def xNorm (v : V) : ℝ :=
  ((∑ u ∈ H.USet v, ((H.kFn v u : ℝ) + (H.lFn v u : ℝ)) / 2) +
    (∑ w ∈ H.WSet v, (H.mFn v w : ℝ))) / (H.cCard v ^ 2)
private noncomputable def t1Norm (v : V) : ℝ :=
  (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u') / (H.cCard v ^ 2)
private noncomputable def t2Norm (v : V) : ℝ :=
  ((∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
    (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u)) / (H.cCard v ^ 2)
private noncomputable def t3Norm (v : V) : ℝ :=
  (∑ w ∈ H.WSet v, ∑ w' ∈ H.WSet v, H.arcInd w w') / (H.cCard v ^ 2)
private noncomputable def m3Norm (v : V) : ℝ :=
  (∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) / (H.cCard v ^ 2)

private lemma cCard_pos {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) : 0 < H.cCard v :=
  Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hc_ge1)

omit [DecidableEq V] in
private lemma kFn_eq (v u : V) : (H.kFn v u : ℝ) = ∑ a ∈ H.ASet v, H.arcInd a u := by
  unfold kFn; rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]; rfl

omit [DecidableEq V] in
private lemma lFn_eq (v u : V) : (H.lFn v u : ℝ) = ∑ b ∈ H.BSet v, H.arcInd u b := by
  unfold lFn; rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]; rfl

omit [DecidableEq V] in
private lemma ms_prod (v u : V) : (H.mFn v u : ℝ) * (H.sFn v u : ℝ) = (H.kFn v u : ℝ) * (H.lFn v u : ℝ) := by
  unfold mFn sFn
  by_cases hkl : H.kFn v u ≤ H.lFn v u
  · rw [Nat.min_eq_left hkl, Nat.max_eq_right hkl]
  · have hlk : H.lFn v u ≤ H.kFn v u := by omega
    rw [Nat.min_eq_right hlk, Nat.max_eq_left hlk, mul_comm]

omit [DecidableEq V] in
private lemma ms_sum (v u : V) : (H.mFn v u : ℝ) + (H.sFn v u : ℝ) = (H.kFn v u : ℝ) + (H.lFn v u : ℝ) := by
  unfold mFn sFn
  by_cases hkl : H.kFn v u ≤ H.lFn v u
  · rw [Nat.min_eq_left hkl, Nat.max_eq_right hkl]
  · have hlk : H.lFn v u ≤ H.kFn v u := by omega
    rw [Nat.min_eq_right hlk, Nat.max_eq_left hlk, add_comm]

private lemma disjoint_USet_WSet (v : V) : Disjoint (H.USet v) (H.WSet v) :=
  finset_disjoint_filter_neg (H.CSet v) _

private lemma union_USet_WSet (v : V) : H.USet v ∪ H.WSet v = H.CSet v :=
  finset_filter_union_neg (H.CSet v) _

private lemma disjoint_WASet_WBSet (v : V) : Disjoint (H.WASet v) (H.WBSet v) :=
  finset_disjoint_filter_neg (H.WSet v) _

private lemma union_WASet_WBSet (v : V) : H.WASet v ∪ H.WBSet v = H.WSet v :=
  finset_filter_union_neg (H.WSet v) _

private lemma one_sub_aNorm {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    1 - H.aNorm v = ((H.WSet v).card : ℝ) / H.cCard v := by
  have hc_pos := H.cCard_pos hc_ge1
  have hcard : ((H.USet v).card : ℝ) + ((H.WSet v).card : ℝ) = H.cCard v := by
    have hn_u := Finset.card_union_of_disjoint (H.disjoint_USet_WSet v)
    rw [H.union_USet_WSet v] at hn_u; unfold cCard; exact_mod_cast hn_u.symm
  unfold aNorm; field_simp [hc_pos.ne']; linarith


private def qWRaw (v : V) : ℝ :=
  (∑ b ∈ H.BSet v, ∑ w ∈ H.WASet v, H.nonAdjInd b w) +
  (∑ a ∈ H.ASet v, ∑ w ∈ H.WBSet v, H.nonAdjInd a w)

private noncomputable def qWNorm (v : V) : ℝ := H.qWRaw v / (H.cCard v ^ 2)

private noncomputable def alphaW (v w : V) : ℝ :=
  (if w ∈ H.WASet v then ∑ w₂ ∈ H.WBSet v, H.arcInd w w₂
   else ∑ w₁ ∈ H.WASet v, H.arcInd w₁ w) / H.cCard v

private lemma pivot_step1_norm_83 {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card)
    (hpivot : (83 / 80 : ℝ) * ((H.CSet v).card : ℝ) ^ 2 +
        (1059 / 680 : ℝ) * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) <
      (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b)) :
    83 / 80 + (1059 / 680) * (H.t1Norm v + H.t2Norm v + H.t3Norm v) < H.gNorm v := by
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos (H.cCard_pos hc_ge1)
  have ht_split : ∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w =
      (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u') +
      ((∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
        (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u)) +
      (∑ w ∈ H.WSet v, ∑ w' ∈ H.WSet v, H.arcInd w w') := by
    conv_lhs => rw [← H.union_USet_WSet v]
    rw [sum_union_sum_union (H.disjoint_USet_WSet v) (H.disjoint_USet_WSet v)]; ring
  have hpiv' : (83 / 80 : ℝ) * H.cCard v ^ 2 +
      (1059 / 680 : ℝ) * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) < H.gRaw v := hpivot
  rw [ht_split] at hpiv'
  have hdiv := (div_lt_div_iff_of_pos_right hc2_pos).mpr hpiv'
  unfold gNorm t1Norm t2Norm t3Norm
  have heq : ((83 / 80 : ℝ) * H.cCard v ^ 2 +
      (1059 / 680 : ℝ) * ((∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u') +
        ((∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
          (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u)) +
        (∑ w ∈ H.WSet v, ∑ w' ∈ H.WSet v, H.arcInd w w'))) / (H.cCard v ^ 2) =
      83 / 80 + (1059 / 680) *
        ((∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u') / (H.cCard v ^ 2) +
        ((∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
          (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u)) / (H.cCard v ^ 2) +
        (∑ w ∈ H.WSet v, ∑ w' ∈ H.WSet v, H.arcInd w w') / (H.cCard v ^ 2)) := by
    rw [add_div, mul_div_cancel_right₀ _ hc2_pos.ne', mul_div_assoc, add_div, add_div]
  linarith

private lemma alphaW_mem_Icc {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) (w : V) :
    0 ≤ H.alphaW v w ∧ H.alphaW v w ≤ 1 := by
  have hc_pos := H.cCard_pos hc_ge1
  unfold alphaW
  constructor
  · refine div_nonneg ?_ hc_pos.le
    split_ifs <;> exact Finset.sum_nonneg fun _ _ => H.arcInd_nonneg _ _
  · rw [div_le_one hc_pos]
    split_ifs
    · calc ∑ w₂ ∈ H.WBSet v, H.arcInd w w₂
          ≤ ∑ _w₂ ∈ H.WBSet v, (1 : ℝ) := Finset.sum_le_sum fun w₂ _ => by
            unfold arcInd; split_ifs <;> norm_num
        _ = ((H.WBSet v).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ H.cCard v := by
            unfold cCard
            exact_mod_cast Finset.card_le_card
              ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    · calc ∑ w₁ ∈ H.WASet v, H.arcInd w₁ w
          ≤ ∑ _w₁ ∈ H.WASet v, (1 : ℝ) := Finset.sum_le_sum fun w₁ _ => by
            unfold arcInd; split_ifs <;> norm_num
        _ = ((H.WASet v).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ H.cCard v := by
            unfold cCard
            exact_mod_cast Finset.card_le_card
              ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

private lemma sum_alphaW_eq {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    (∑ w ∈ H.WSet v, H.alphaW v w) / H.cCard v = 2 * H.m3Norm v := by
  have hc_pos := H.cCard_pos hc_ge1
  rw [← H.union_WASet_WBSet v, Finset.sum_union (H.disjoint_WASet_WBSet v)]
  have h1 : ∑ w ∈ H.WASet v, H.alphaW v w =
      (∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) / H.cCard v := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun w hw => by simp only [alphaW, hw, ↓reduceIte]
  have h2 : ∑ w ∈ H.WBSet v, H.alphaW v w =
      (∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) / H.cCard v := by
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hnot : w ∉ H.WASet v := fun h => Finset.disjoint_left.mp (H.disjoint_WASet_WBSet v) h hw
    simp only [alphaW, hnot, ↓reduceIte]
  rw [h1, h2]; unfold m3Norm; field_simp [hc_pos.ne']; ring

/-- **Brand-New `C₃`-Exclusion Non-Edge Lemma**:
For any directed edge `u → w` in `C(v)`, every `a ∈ A(v)` with `a → u` cannot satisfy `w → a`
(else `a → u → w → a` is a `C₃`), so `k(u) - k(w) ≤ q_A(w)` and symmetrically `l(w) - l(u) ≤ q_B(u)`. -/
private lemma c3_excl_k_diff (hH : H.TriangleFree) {v u w : V}
    (hw : w ∈ H.CSet v) (huw : H.adj u w) :
    (H.kFn v u : ℝ) - (H.kFn v w : ℝ) ≤ ∑ a ∈ H.ASet v, H.nonAdjInd a w := by
  rw [H.kFn_eq v u, H.kFn_eq v w, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun a ha => ?_
  have hne : a ≠ w := fun h => by
    subst h; exact Finset.disjoint_left.mp (H.disjoint_ASet_CSet v) ha hw
  have htri := H.arc_add_arc_add_nonAdj hne
  by_cases hau : H.adj a u
  · have hnwa : ¬ H.adj w a := fun hwa => hH ⟨a, u, w, hau, huw, hwa⟩
    have hwa0 : H.arcInd w a = 0 := by simp [arcInd, hnwa]
    have hau1 : H.arcInd a u = 1 := by simp [arcInd, hau]
    linarith
  · have hau0 : H.arcInd a u = 0 := by simp [arcInd, hau]
    linarith [H.arcInd_nonneg a w, H.nonAdjInd_nonneg a w]

private lemma c3_excl_l_diff (hH : H.TriangleFree) {v u w : V}
    (hu : u ∈ H.CSet v) (huw : H.adj u w) :
    (H.lFn v w : ℝ) - (H.lFn v u : ℝ) ≤ ∑ b ∈ H.BSet v, H.nonAdjInd b u := by
  rw [H.lFn_eq v w, H.lFn_eq v u, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun b hb => ?_
  have hne : b ≠ u := fun h => by
    subst h; exact Finset.disjoint_left.mp (H.disjoint_BSet_CSet v) hb hu
  have htri := H.arc_add_arc_add_nonAdj hne
  by_cases hwb : H.adj w b
  · have hnbu : ¬ H.adj b u := fun hbu => hH ⟨u, w, b, huw, hwb, hbu⟩
    have hbu0 : H.arcInd b u = 0 := by simp [arcInd, hnbu]
    have hwb1 : H.arcInd w b = 1 := by simp [arcInd, hwb]
    linarith
  · have hwb0 : H.arcInd w b = 0 := by simp [arcInd, hwb]
    linarith [H.arcInd_nonneg u b, H.nonAdjInd_nonneg b u]

/-- Aggregated branch-free `C₃`-exclusion inequality over `W_A → W_B` (dividing by `c ≥ 1`). -/
private lemma c3_excl_W_bound (hH : H.TriangleFree) {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    (∑ w ∈ H.WSet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v)) / H.cCard v ≤
      H.qWNorm v := by
  have hc_pos := H.cCard_pos hc_ge1
  have hc3_pos : 0 < H.cCard v ^ 3 := by positivity
  have h_raw_le :
      (∑ w₁ ∈ H.WASet v, (∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ))) +
      (∑ w₂ ∈ H.WBSet v, (∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂) * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ))) ≤
      H.cCard v * H.qWRaw v := by
    have h_eq_pair :
        (∑ w₁ ∈ H.WASet v, (∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ))) +
        (∑ w₂ ∈ H.WBSet v, (∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂) * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ))) =
        ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v,
          H.arcInd w₁ w₂ * (((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ)) + ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ))) := by
      have h1 : ∑ w₁ ∈ H.WASet v, (∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ)) =
          ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂ * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ)) :=
        Finset.sum_congr rfl fun w₁ _ => Finset.sum_mul _ _ _
      have h2 : ∑ w₂ ∈ H.WBSet v, (∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂) * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ)) =
          ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂ * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ)) := by
        rw [Finset.sum_congr rfl fun w₂ _ => Finset.sum_mul _ _ _, Finset.sum_comm]
      rw [h1, h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w₁ _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w₂ _ => by ring
    have h_pair_le :
        ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v,
          H.arcInd w₁ w₂ * (((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ)) + ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ))) ≤
        ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v,
          (H.arcInd w₁ w₂ * (∑ b ∈ H.BSet v, H.nonAdjInd b w₁) +
           H.arcInd w₁ w₂ * (∑ a ∈ H.ASet v, H.nonAdjInd a w₂)) := by
      refine Finset.sum_le_sum fun w₁ hw₁ => Finset.sum_le_sum fun w₂ hw₂ => ?_
      by_cases hadj : H.adj w₁ w₂
      · have h1 : H.arcInd w₁ w₂ = 1 := by simp [arcInd, hadj]
        have hle1 : H.lFn v w₁ ≤ H.kFn v w₁ := (Finset.mem_filter.mp hw₁).2
        have hlt2 : ¬ (H.lFn v w₂ ≤ H.kFn v w₂) := (Finset.mem_filter.mp hw₂).2
        have hs1 : (H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ) = (H.kFn v w₁ : ℝ) - (H.lFn v w₁ : ℝ) := by
          unfold sFn mFn; rw [Nat.max_eq_left hle1, Nat.min_eq_right hle1]
        have hs2 : (H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ) = (H.lFn v w₂ : ℝ) - (H.kFn v w₂ : ℝ) := by
          unfold sFn mFn; rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
        have hw₁C : w₁ ∈ H.CSet v := Finset.filter_subset _ _ (Finset.filter_subset _ _ hw₁)
        have hw₂C : w₂ ∈ H.CSet v := Finset.filter_subset _ _ (Finset.filter_subset _ _ hw₂)
        have hk := H.c3_excl_k_diff hH hw₂C hadj
        have hl := H.c3_excl_l_diff hH hw₁C hadj
        rw [h1, hs1, hs2]; linarith
      · have h0 : H.arcInd w₁ w₂ = 0 := by simp [arcInd, hadj]
        simp [h0]
    have h_rhs_le :
        ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v,
          (H.arcInd w₁ w₂ * (∑ b ∈ H.BSet v, H.nonAdjInd b w₁) +
           H.arcInd w₁ w₂ * (∑ a ∈ H.ASet v, H.nonAdjInd a w₂)) ≤
        H.cCard v * H.qWRaw v := by
      simp_rw [Finset.sum_add_distrib]
      have hA_part : ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂ * (∑ b ∈ H.BSet v, H.nonAdjInd b w₁) ≤
          H.cCard v * (∑ b ∈ H.BSet v, ∑ w₁ ∈ H.WASet v, H.nonAdjInd b w₁) := by
        rw [Finset.sum_comm (s := H.BSet v) (t := H.WASet v), Finset.mul_sum]
        refine Finset.sum_le_sum fun w₁ _ => ?_
        rw [← Finset.sum_mul]
        have hnn : 0 ≤ ∑ b ∈ H.BSet v, H.nonAdjInd b w₁ :=
          Finset.sum_nonneg fun b _ => H.nonAdjInd_nonneg b w₁
        have hdeg : ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂ ≤ H.cCard v := by
          calc ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂
              ≤ ∑ _w₂ ∈ H.WBSet v, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by
                unfold arcInd; split_ifs <;> norm_num
            _ = ((H.WBSet v).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ H.cCard v := by
                unfold cCard
                exact_mod_cast Finset.card_le_card
                  ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        exact mul_le_mul_of_nonneg_right hdeg hnn
      have hB_part : ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂ * (∑ a ∈ H.ASet v, H.nonAdjInd a w₂) ≤
          H.cCard v * (∑ a ∈ H.ASet v, ∑ w₂ ∈ H.WBSet v, H.nonAdjInd a w₂) := by
        rw [Finset.sum_comm, Finset.sum_comm (s := H.ASet v) (t := H.WBSet v), Finset.mul_sum]
        refine Finset.sum_le_sum fun w₂ _ => ?_
        rw [← Finset.sum_mul]
        have hnn : 0 ≤ ∑ a ∈ H.ASet v, H.nonAdjInd a w₂ :=
          Finset.sum_nonneg fun a _ => H.nonAdjInd_nonneg a w₂
        have hdeg : ∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂ ≤ H.cCard v := by
          calc ∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂
              ≤ ∑ _w₁ ∈ H.WASet v, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by
                unfold arcInd; split_ifs <;> norm_num
            _ = ((H.WASet v).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ H.cCard v := by
                unfold cCard
                exact_mod_cast Finset.card_le_card
                  ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        exact mul_le_mul_of_nonneg_right hdeg hnn
      unfold qWRaw; linarith
    linarith [h_eq_pair, h_pair_le, h_rhs_le]
  have h_lhs_id :
      (∑ w ∈ H.WSet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v)) / H.cCard v =
      ((∑ w₁ ∈ H.WASet v, (∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ))) +
       (∑ w₂ ∈ H.WBSet v, (∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂) * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ)))) /
        (H.cCard v ^ 3) := by
    rw [← H.union_WASet_WBSet v, Finset.sum_union (H.disjoint_WASet_WBSet v)]
    have h1 : ∑ w ∈ H.WASet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v) =
        (∑ w₁ ∈ H.WASet v, (∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ))) /
          (H.cCard v ^ 2) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun w hw => ?_
      simp only [alphaW, hw, ↓reduceIte]; ring
    have h2 : ∑ w ∈ H.WBSet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v) =
        (∑ w₂ ∈ H.WBSet v, (∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂) * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ))) /
          (H.cCard v ^ 2) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hnot : w ∉ H.WASet v := fun h => Finset.disjoint_left.mp (H.disjoint_WASet_WBSet v) h hw
      simp only [alphaW, hnot, ↓reduceIte]; ring
    rw [h1, h2]; field_simp [hc_pos.ne']
  rw [h_lhs_id]; unfold qWNorm
  calc ((∑ w₁ ∈ H.WASet v, (∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂) * ((H.sFn v w₁ : ℝ) - (H.mFn v w₁ : ℝ))) +
        (∑ w₂ ∈ H.WBSet v, (∑ w₁ ∈ H.WASet v, H.arcInd w₁ w₂) * ((H.sFn v w₂ : ℝ) - (H.mFn v w₂ : ℝ)))) /
          (H.cCard v ^ 3)
      ≤ (H.cCard v * H.qWRaw v) / (H.cCard v ^ 3) := div_le_div_of_nonneg_right h_raw_le hc3_pos.le
    _ = H.qWRaw v / (H.cCard v ^ 2) := by field_simp [hc_pos.ne']

private lemma pivot_step3_83 (hH : H.TriangleFree) {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    H.gNorm v - (100 / 83) * H.xNorm v + H.qWNorm v ≥
      (13 / 25) * H.gNorm v - (197 / 250) * H.aNorm v - (101 / 200) * (1 - H.aNorm v) +
        (33 / 50) * H.m3Norm v := by
  have hc_pos := H.cCard_pos hc_ge1
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos hc_pos
  have hu_sum : ∑ u ∈ H.USet v, (100 / 83 : ℝ) * (((H.kFn v u : ℝ) + (H.lFn v u : ℝ)) / (2 * H.cCard v)) ≤
      ∑ u ∈ H.USet v, ((12 / 25 : ℝ) * ((H.mFn v u : ℝ) * (H.sFn v u : ℝ) / (H.cCard v ^ 2)) + 197 / 250) := by
    refine Finset.sum_le_sum fun u hu => ?_
    have hu_f : 2 * (H.sFn v u : ℝ) ≤ 3 * (H.mFn v u : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hu).2
    have hm_le_s : (H.mFn v u : ℝ) ≤ (H.sFn v u : ℝ) := by
      have hnat : H.mFn v u ≤ H.sFn v u := le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)
      exact_mod_cast hnat
    rw [← H.ms_sum v u]
    exact step3_u_algebra_83 hc_pos (Nat.cast_nonneg _) hm_le_s hu_f
  have hw_sum : ∑ w ∈ H.WSet v,
      ((100 / 83 : ℝ) * ((H.mFn v w : ℝ) / H.cCard v) -
        H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v)) ≤
      ∑ w ∈ H.WSet v, ((12 / 25 : ℝ) * ((H.mFn v w : ℝ) * (H.sFn v w : ℝ) / (H.cCard v ^ 2)) +
        101 / 200 - (33 / 100) * H.alphaW v w) := by
    refine Finset.sum_le_sum fun w hw => ?_
    have hw_f : ¬ (2 * H.sFn v w ≤ 3 * H.mFn v w) := (Finset.mem_filter.mp hw).2
    have h32 : 3 * (H.mFn v w : ℝ) ≤ 2 * (H.sFn v w : ℝ) := by
      have : 3 * H.mFn v w ≤ 2 * H.sFn v w := by omega
      exact_mod_cast this
    have h0 := step3_w0_algebra_83 hc_pos (Nat.cast_nonneg _) h32
    have h1 := step3_w1_algebra_83 hc_pos (Nat.cast_nonneg _) h32
    rcases H.alphaW_mem_Icc hc_ge1 w with ⟨ha0, ha1⟩
    nlinarith
  have hms_total : ∑ u ∈ H.CSet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ) ≤ H.cCard v * H.gRaw v := by
    simp_rw [H.ms_prod v, H.kFn_eq v, H.lFn_eq v]
    exact H.step2_kl_sum_le hH v
  have hms_split : (∑ u ∈ H.USet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) +
      (∑ w ∈ H.WSet v, (H.mFn v w : ℝ) * (H.sFn v w : ℝ)) =
      ∑ u ∈ H.CSet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ) :=
    (Finset.sum_union (H.disjoint_USet_WSet v)).symm.trans (by rw [H.union_USet_WSet v])
  have hu_lhs : ∑ u ∈ H.USet v, (100 / 83 : ℝ) * (((H.kFn v u : ℝ) + (H.lFn v u : ℝ)) / (2 * H.cCard v)) =
      (100 / 83 : ℝ) * ((∑ u ∈ H.USet v, ((H.kFn v u : ℝ) + (H.lFn v u : ℝ))) / (2 * H.cCard v)) := by
    rw [← Finset.mul_sum, ← Finset.sum_div]
  have hu_rhs : ∑ u ∈ H.USet v, ((12 / 25 : ℝ) * ((H.mFn v u : ℝ) * (H.sFn v u : ℝ) / (H.cCard v ^ 2)) + 197 / 250) =
      (12 / 25 : ℝ) * ((∑ u ∈ H.USet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) / (H.cCard v ^ 2)) +
        ((H.USet v).card : ℝ) * (197 / 250) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
  have hw_lhs : ∑ w ∈ H.WSet v,
      ((100 / 83 : ℝ) * ((H.mFn v w : ℝ) / H.cCard v) -
        H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v)) =
      (100 / 83 : ℝ) * ((∑ w ∈ H.WSet v, (H.mFn v w : ℝ)) / H.cCard v) -
      ∑ w ∈ H.WSet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have hw_rhs : ∑ w ∈ H.WSet v, ((12 / 25 : ℝ) * ((H.mFn v w : ℝ) * (H.sFn v w : ℝ) / (H.cCard v ^ 2)) +
        101 / 200 - (33 / 100) * H.alphaW v w) =
      (12 / 25 : ℝ) * ((∑ w ∈ H.WSet v, (H.mFn v w : ℝ) * (H.sFn v w : ℝ)) / (H.cCard v ^ 2)) +
        ((H.WSet v).card : ℝ) * (101 / 200) - (33 / 100) * (∑ w ∈ H.WSet v, H.alphaW v w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hu_lhs, hu_rhs] at hu_sum
  rw [hw_lhs, hw_rhs] at hw_sum
  have hdiv_c := div_le_div_of_nonneg_right (add_le_add hu_sum hw_sum) hc_pos.le
  have h_lhs_eq : ((100 / 83 : ℝ) * ((∑ u ∈ H.USet v, ((H.kFn v u : ℝ) + (H.lFn v u : ℝ))) / (2 * H.cCard v)) +
      ((100 / 83 : ℝ) * ((∑ w ∈ H.WSet v, (H.mFn v w : ℝ)) / H.cCard v) -
        ∑ w ∈ H.WSet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v))) / H.cCard v =
      (100 / 83) * H.xNorm v -
        (∑ w ∈ H.WSet v, H.alphaW v w * (((H.sFn v w : ℝ) - (H.mFn v w : ℝ)) / H.cCard v)) / H.cCard v := by
    unfold xNorm; rw [← Finset.sum_div]; field_simp [hc_pos.ne']; ring
  have h12 : (((∑ u ∈ H.USet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) +
      (∑ w ∈ H.WSet v, (H.mFn v w : ℝ) * (H.sFn v w : ℝ))) / H.cCard v ^ 2) / H.cCard v ≤ H.gNorm v := by
    rw [hms_split]; unfold gNorm
    calc ((∑ u ∈ H.CSet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) / H.cCard v ^ 2) / H.cCard v
        ≤ ((H.cCard v * H.gRaw v) / H.cCard v ^ 2) / H.cCard v :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hms_total hc2_pos.le) hc_pos.le
      _ = H.gRaw v / H.cCard v ^ 2 := by field_simp [hc_pos.ne']
  have h_rhs_le : (((12 / 25 : ℝ) * ((∑ u ∈ H.USet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) / H.cCard v ^ 2) +
      ((H.USet v).card : ℝ) * (197 / 250)) +
      ((12 / 25 : ℝ) * ((∑ w ∈ H.WSet v, (H.mFn v w : ℝ) * (H.sFn v w : ℝ)) / H.cCard v ^ 2) +
      ((H.WSet v).card : ℝ) * (101 / 200) - (33 / 100) * (∑ w ∈ H.WSet v, H.alphaW v w))) / H.cCard v ≤
      (12 / 25) * H.gNorm v + (197 / 250) * H.aNorm v + (101 / 200) * (1 - H.aNorm v) -
        (33 / 50) * H.m3Norm v := by
    have hw_c : ((H.WSet v).card : ℝ) / H.cCard v = 1 - H.aNorm v := (H.one_sub_aNorm hc_ge1).symm
    have ha_c : ((H.USet v).card : ℝ) / H.cCard v = H.aNorm v := rfl
    have hm3_c : (∑ w ∈ H.WSet v, H.alphaW v w) / H.cCard v = 2 * H.m3Norm v := H.sum_alphaW_eq hc_ge1
    have hrearr : (((12 / 25 : ℝ) * ((∑ u ∈ H.USet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) / H.cCard v ^ 2) +
        ((H.USet v).card : ℝ) * (197 / 250)) +
        ((12 / 25 : ℝ) * ((∑ w ∈ H.WSet v, (H.mFn v w : ℝ) * (H.sFn v w : ℝ)) / H.cCard v ^ 2) +
        ((H.WSet v).card : ℝ) * (101 / 200) - (33 / 100) * (∑ w ∈ H.WSet v, H.alphaW v w))) / H.cCard v =
        (12 / 25 : ℝ) * ((((∑ u ∈ H.USet v, (H.mFn v u : ℝ) * (H.sFn v u : ℝ)) +
          (∑ w ∈ H.WSet v, (H.mFn v w : ℝ) * (H.sFn v w : ℝ))) / H.cCard v ^ 2) / H.cCard v) +
        (((H.USet v).card : ℝ) / H.cCard v) * (197 / 250) +
        (((H.WSet v).card : ℝ) / H.cCard v) * (101 / 200) -
        (33 / 100) * ((∑ w ∈ H.WSet v, H.alphaW v w) / H.cCard v) := by
      field_simp [hc_pos.ne']; ring
    rw [hrearr, ha_c, hw_c, hm3_c]; linarith
  have hqW := H.c3_excl_W_bound hH hc_ge1
  linarith [hdiv_c, h_lhs_eq, h_rhs_le, hqW]

private lemma pivot_t2_le {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    H.t2Norm v ≤ H.aNorm v * (1 - H.aNorm v) := by
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos (H.cCard_pos hc_ge1)
  rw [H.one_sub_aNorm hc_ge1]; unfold t2Norm aNorm
  have hsum_le : (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
      (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u) ≤
      ((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ) := by
    rw [Finset.sum_comm (s := H.WSet v) (t := H.USet v), ← Finset.sum_add_distrib]
    have hpt : ∀ u ∈ H.USet v, ∑ w ∈ H.WSet v, (H.arcInd u w + H.arcInd w u) ≤ ((H.WSet v).card : ℝ) := by
      intro u hu
      calc ∑ w ∈ H.WSet v, (H.arcInd u w + H.arcInd w u)
          ≤ ∑ _w ∈ H.WSet v, (1 : ℝ) := Finset.sum_le_sum fun w hw => by
            have hne : u ≠ w := fun h => by
              subst h; exact Finset.disjoint_left.mp (H.disjoint_USet_WSet v) hu hw
            linarith [H.arc_add_arc_add_nonAdj hne, H.nonAdjInd_nonneg u w]
        _ = ((H.WSet v).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    calc ∑ u ∈ H.USet v, (∑ w ∈ H.WSet v, H.arcInd u w + ∑ w ∈ H.WSet v, H.arcInd w u)
        = ∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, (H.arcInd u w + H.arcInd w u) :=
          Finset.sum_congr rfl fun u _ => (Finset.sum_add_distrib).symm
      _ ≤ ∑ _u ∈ H.USet v, ((H.WSet v).card : ℝ) := Finset.sum_le_sum hpt
      _ = ((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
        (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u)) / (H.cCard v ^ 2)
      ≤ (((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ)) / (H.cCard v ^ 2) :=
        div_le_div_of_nonneg_right hsum_le hc2_pos.le
    _ = (((H.USet v).card : ℝ) / H.cCard v) * (((H.WSet v).card : ℝ) / H.cCard v) := by ring

private lemma pivot_m3_le_t3 {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    H.m3Norm v ≤ H.t3Norm v := by
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos (H.cCard_pos hc_ge1)
  unfold m3Norm t3Norm
  refine div_le_div_of_nonneg_right ?_ hc2_pos.le
  calc ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂
      ≤ ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WSet v, H.arcInd w₁ w₂ :=
        Finset.sum_le_sum fun w₁ _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun w₂ _ _ => H.arcInd_nonneg w₁ w₂)
    _ ≤ ∑ w₁ ∈ H.WSet v, ∑ w₂ ∈ H.WSet v, H.arcInd w₁ w₂ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun w₁ _ _ => Finset.sum_nonneg fun w₂ _ => H.arcInd_nonneg w₁ w₂)

private lemma pivot_exp_tau {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) (side : V → Bool)
    (hWA : ∀ w ∈ H.WASet v, side w = true) (hWB : ∀ w ∈ H.WBSet v, side w = false) :
    H.tauReal v side =
      (∑ a₀ ∈ H.ASet v, ∑ u ∈ H.USet v, (if side u = false then 1 else 0) * H.arcInd a₀ u) +
      (∑ u ∈ H.USet v, ∑ b₀ ∈ H.BSet v, (if side u = true then 1 else 0) * H.arcInd u b₀) +
      (∑ w ∈ H.WSet v, (H.mFn v w : ℝ)) +
      (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if side u = true ∧ side u' = false then 1 else 0) * H.arcInd u u') +
      (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if side u = true then 1 else 0) * H.arcInd u w) +
      (∑ w ∈ H.WASet v, ∑ u ∈ H.USet v, (if side u = false then 1 else 0) * H.arcInd w u) +
      H.cCard v ^ 2 * H.m3Norm v := by
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos (H.cCard_pos hc_ge1)
  have hgW : (∑ a₀ ∈ H.ASet v, ∑ w ∈ H.WSet v, (if side w = false then 1 else 0) * H.arcInd a₀ w) +
      (∑ w ∈ H.WSet v, ∑ b₀ ∈ H.BSet v, (if side w = true then 1 else 0) * H.arcInd w b₀) =
      ∑ w ∈ H.WSet v, (H.mFn v w : ℝ) := by
    rw [Finset.sum_comm (s := H.ASet v) (t := H.WSet v)]
    simp_rw [← Finset.mul_sum, ← H.kFn_eq v, ← H.lFn_eq v]
    rw [← H.union_WASet_WBSet v, Finset.sum_union (H.disjoint_WASet_WBSet v),
      Finset.sum_union (H.disjoint_WASet_WBSet v), Finset.sum_union (H.disjoint_WASet_WBSet v)]
    have h1 : ∑ w ∈ H.WASet v, (if side w = false then (1 : ℝ) else 0) * (H.kFn v w : ℝ) = 0 :=
      Finset.sum_eq_zero fun w hw => by rw [hWA w hw]; simp
    have h2 : ∑ w ∈ H.WBSet v, (if side w = false then (1 : ℝ) else 0) * (H.kFn v w : ℝ) =
        ∑ w ∈ H.WBSet v, (H.mFn v w : ℝ) :=
      Finset.sum_congr rfl fun w hw => by
        rw [hWB w hw]; simp only [↓reduceIte, one_mul]
        have hgt : ¬ (H.lFn v w ≤ H.kFn v w) := (Finset.mem_filter.mp hw).2
        unfold mFn; rw [Nat.min_eq_left (by omega)]
    have h3 : ∑ w ∈ H.WASet v, (if side w = true then (1 : ℝ) else 0) * (H.lFn v w : ℝ) =
        ∑ w ∈ H.WASet v, (H.mFn v w : ℝ) :=
      Finset.sum_congr rfl fun w hw => by
        rw [hWA w hw]; simp only [↓reduceIte, one_mul]
        have hle : H.lFn v w ≤ H.kFn v w := (Finset.mem_filter.mp hw).2
        unfold mFn; rw [Nat.min_eq_right hle]
    have h4 : ∑ w ∈ H.WBSet v, (if side w = true then (1 : ℝ) else 0) * (H.lFn v w : ℝ) = 0 :=
      Finset.sum_eq_zero fun w hw => by rw [hWB w hw]; simp
    linarith
  unfold tauReal
  rw [← H.union_USet_WSet v, sum_inner_union (H.ASet v) (H.disjoint_USet_WSet v),
    Finset.sum_union (H.disjoint_USet_WSet v),
    sum_union_sum_union (H.disjoint_USet_WSet v) (H.disjoint_USet_WSet v)]
  have hUW : ∑ u ∈ H.USet v, ∑ w ∈ H.WSet v,
      (if side u = true ∧ side w = false then 1 else 0) * H.arcInd u w =
      ∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if side u = true then 1 else 0) * H.arcInd u w := by
    rw [← H.union_WASet_WBSet v, sum_inner_union (H.USet v) (H.disjoint_WASet_WBSet v)]
    have h0 : ∑ u ∈ H.USet v, ∑ w ∈ H.WASet v,
        (if side u = true ∧ side w = false then 1 else 0) * H.arcInd u w = 0 :=
      Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun w hw => by rw [hWA w hw]; simp
    have h1 : ∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v,
        (if side u = true ∧ side w = false then 1 else 0) * H.arcInd u w =
        ∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if side u = true then 1 else 0) * H.arcInd u w :=
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w hw => by rw [hWB w hw]; simp
    linarith
  have hWU : ∑ w ∈ H.WSet v, ∑ u ∈ H.USet v,
      (if side w = true ∧ side u = false then 1 else 0) * H.arcInd w u =
      ∑ w ∈ H.WASet v, ∑ u ∈ H.USet v, (if side u = false then 1 else 0) * H.arcInd w u := by
    rw [← H.union_WASet_WBSet v, Finset.sum_union (H.disjoint_WASet_WBSet v)]
    have h1 : ∑ w ∈ H.WASet v, ∑ u ∈ H.USet v,
        (if side w = true ∧ side u = false then 1 else 0) * H.arcInd w u =
        ∑ w ∈ H.WASet v, ∑ u ∈ H.USet v, (if side u = false then 1 else 0) * H.arcInd w u :=
      Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun u _ => by rw [hWA w hw]; simp
    have h0 : ∑ w ∈ H.WBSet v, ∑ u ∈ H.USet v,
        (if side w = true ∧ side u = false then 1 else 0) * H.arcInd w u = 0 :=
      Finset.sum_eq_zero fun w hw => Finset.sum_eq_zero fun u _ => by rw [hWB w hw]; simp
    linarith
  have hWW : ∑ w₁ ∈ H.WSet v, ∑ w₂ ∈ H.WSet v,
      (if side w₁ = true ∧ side w₂ = false then 1 else 0) * H.arcInd w₁ w₂ =
      H.cCard v ^ 2 * H.m3Norm v := by
    rw [← H.union_WASet_WBSet v,
      sum_union_sum_union (H.disjoint_WASet_WBSet v) (H.disjoint_WASet_WBSet v)]
    have hAA : ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WASet v,
        (if side w₁ = true ∧ side w₂ = false then 1 else 0) * H.arcInd w₁ w₂ = 0 :=
      Finset.sum_eq_zero fun w₁ _ => Finset.sum_eq_zero fun w₂ hw₂ => by rw [hWA w₂ hw₂]; simp
    have hBA : ∑ w₁ ∈ H.WBSet v, ∑ w₂ ∈ H.WASet v,
        (if side w₁ = true ∧ side w₂ = false then 1 else 0) * H.arcInd w₁ w₂ = 0 :=
      Finset.sum_eq_zero fun w₁ hw₁ => Finset.sum_eq_zero fun w₂ _ => by rw [hWB w₁ hw₁]; simp
    have hBB : ∑ w₁ ∈ H.WBSet v, ∑ w₂ ∈ H.WBSet v,
        (if side w₁ = true ∧ side w₂ = false then 1 else 0) * H.arcInd w₁ w₂ = 0 :=
      Finset.sum_eq_zero fun w₁ hw₁ => Finset.sum_eq_zero fun w₂ _ => by rw [hWB w₁ hw₁]; simp
    have hAB : ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v,
        (if side w₁ = true ∧ side w₂ = false then 1 else 0) * H.arcInd w₁ w₂ =
        H.cCard v ^ 2 * H.m3Norm v := by
      have heq : ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v,
          (if side w₁ = true ∧ side w₂ = false then 1 else 0) * H.arcInd w₁ w₂ =
          ∑ w₁ ∈ H.WASet v, ∑ w₂ ∈ H.WBSet v, H.arcInd w₁ w₂ :=
        Finset.sum_congr rfl fun w₁ hw₁ => Finset.sum_congr rfl fun w₂ hw₂ => by
          rw [hWA w₁ hw₁, hWB w₂ hw₂]; simp
      rw [heq]; unfold m3Norm; exact (mul_div_cancel₀ _ hc2_pos.ne').symm
    linarith
  linarith [hgW, hUW, hWU, hWW]

private lemma pivot_UW_nonAdj_id {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, H.nonAdjInd u w) +
      (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, H.nonAdjInd u w) =
      ((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ) - H.cCard v ^ 2 * H.t2Norm v := by
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos (H.cCard_pos hc_ge1)
  rw [← sum_inner_union (H.USet v) (H.disjoint_WASet_WBSet v), H.union_WASet_WBSet v]
  have htot : ∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, (H.arcInd u w + H.arcInd w u + H.nonAdjInd u w) =
      ((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ) := by
    have hp : ∀ u ∈ H.USet v, ∀ w ∈ H.WSet v, H.arcInd u w + H.arcInd w u + H.nonAdjInd u w = 1 :=
      fun u hu w hw => H.arc_add_arc_add_nonAdj
        (fun h => by subst h; exact Finset.disjoint_left.mp (H.disjoint_USet_WSet v) hu hw)
    have hp2 : ∀ u ∈ H.USet v, ∑ w ∈ H.WSet v, (H.arcInd u w + H.arcInd w u + H.nonAdjInd u w) =
        ((H.WSet v).card : ℝ) :=
      fun u hu => by rw [Finset.sum_congr rfl (hp u hu), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl hp2, Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.sum_add_distrib] at htot
  have ht2_eq : H.cCard v ^ 2 * H.t2Norm v =
      (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
      (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd w u) := by
    unfold t2Norm
    rw [mul_div_cancel₀ _ hc2_pos.ne', Finset.sum_comm (s := H.WSet v) (t := H.USet v)]
  linarith


private def side3Cut (v : V) (ω : V → Bool) (z : V) : Bool :=
  if z ∈ H.USet v then ω z else decide (z ∈ H.WASet v)

private lemma pivot_cut3_rho_83 {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    omegaCard V * (2 * H.gRaw v + 2 * H.qWRaw v +
      H.aNorm v ^ 2 * H.cCard v ^ 2 / 2 - H.cCard v ^ 2 * H.t1Norm v +
      (((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ) - H.cCard v ^ 2 * H.t2Norm v)) ≤
      ∑ ω : V → Bool, H.ordRhoReal v (H.side3Cut v ω) := by
  have hc_pos := H.cCard_pos hc_ge1
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos hc_pos
  let K : ℝ := omegaCard V
  have hpt_rho : ∀ ω : V → Bool,
      2 * H.cCard v + 2 * H.gRaw v + 2 * H.qWRaw v +
        (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u ≠ ω u' then 1 else 0) * H.nonAdjInd u u') +
        2 * (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, (if ω u = false then 1 else 0) * H.nonAdjInd u w) +
        2 * (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if ω u = true then 1 else 0) * H.nonAdjInd u w) ≤
      H.ordRhoReal v (H.side3Cut v ω) := by
    intro ω
    unfold ordRhoReal
    have hAC_keep : 2 * (∑ a₀ ∈ H.ASet v, ∑ w ∈ H.WBSet v, H.nonAdjInd a₀ w) ≤
        2 * (∑ a₀ ∈ H.ASet v, ∑ u ∈ H.CSet v,
          (if H.side3Cut v ω u = false then 1 else 0) * H.nonAdjInd a₀ u) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a₀ _ => ?_) (by norm_num)
      have hsub : H.WBSet v ⊆ H.CSet v := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      calc ∑ w ∈ H.WBSet v, H.nonAdjInd a₀ w
          = ∑ w ∈ H.WBSet v, (if H.side3Cut v ω w = false then 1 else 0) * H.nonAdjInd a₀ w := by
            refine Finset.sum_congr rfl fun w hw => ?_
            have hwU : w ∉ H.USet v := fun h =>
              Finset.disjoint_left.mp (H.disjoint_USet_WSet v) h (Finset.filter_subset _ _ hw)
            have hwWA : w ∉ H.WASet v := fun h =>
              Finset.disjoint_left.mp (H.disjoint_WASet_WBSet v) h hw
            simp only [side3Cut, hwU, ↓reduceIte, decide_eq_false hwWA, one_mul]
        _ ≤ ∑ u ∈ H.CSet v, (if H.side3Cut v ω u = false then 1 else 0) * H.nonAdjInd a₀ u :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ =>
              mul_nonneg (by split_ifs <;> norm_num) (H.nonAdjInd_nonneg a₀ u)
    have hBC_keep : 2 * (∑ b₀ ∈ H.BSet v, ∑ w ∈ H.WASet v, H.nonAdjInd b₀ w) ≤
        2 * (∑ b₀ ∈ H.BSet v, ∑ u ∈ H.CSet v,
          (if H.side3Cut v ω u = true then 1 else 0) * H.nonAdjInd b₀ u) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₀ _ => ?_) (by norm_num)
      have hsub : H.WASet v ⊆ H.CSet v := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      calc ∑ w ∈ H.WASet v, H.nonAdjInd b₀ w
          = ∑ w ∈ H.WASet v, (if H.side3Cut v ω w = true then 1 else 0) * H.nonAdjInd b₀ w := by
            refine Finset.sum_congr rfl fun w hw => ?_
            have hwU : w ∉ H.USet v := fun h =>
              Finset.disjoint_left.mp (H.disjoint_USet_WSet v) h (Finset.filter_subset _ _ hw)
            simp only [side3Cut, hwU, ↓reduceIte, decide_eq_true hw, one_mul]
        _ ≤ ∑ u ∈ H.CSet v, (if H.side3Cut v ω u = true then 1 else 0) * H.nonAdjInd b₀ u :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ =>
              mul_nonneg (by split_ifs <;> norm_num) (H.nonAdjInd_nonneg b₀ u)
    have hCC : (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u ≠ ω u' then 1 else 0) * H.nonAdjInd u u') +
        2 * (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, (if ω u = false then 1 else 0) * H.nonAdjInd u w) +
        2 * (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if ω u = true then 1 else 0) * H.nonAdjInd u w) ≤
        ∑ z₁ ∈ H.CSet v, ∑ z₂ ∈ H.CSet v,
          (if H.side3Cut v ω z₁ ≠ H.side3Cut v ω z₂ then 1 else 0) * H.nonAdjInd z₁ z₂ := by
      rw [← H.union_USet_WSet v,
        sum_union_sum_union (H.disjoint_USet_WSet v) (H.disjoint_USet_WSet v)]
      have hUU : ∑ z₁ ∈ H.USet v, ∑ z₂ ∈ H.USet v,
          (if H.side3Cut v ω z₁ ≠ H.side3Cut v ω z₂ then 1 else 0) * H.nonAdjInd z₁ z₂ =
          ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u ≠ ω u' then 1 else 0) * H.nonAdjInd u u' :=
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => by
          simp only [side3Cut, hu, hu', ↓reduceIte]
      have hWW : 0 ≤ ∑ z₁ ∈ H.WSet v, ∑ z₂ ∈ H.WSet v,
          (if H.side3Cut v ω z₁ ≠ H.side3Cut v ω z₂ then 1 else 0) * H.nonAdjInd z₁ z₂ :=
        Finset.sum_nonneg fun z₁ _ => Finset.sum_nonneg fun z₂ _ =>
          mul_nonneg (by split_ifs <;> norm_num) (H.nonAdjInd_nonneg z₁ z₂)
      have hUW_eq : ∑ z₁ ∈ H.USet v, ∑ z₂ ∈ H.WSet v,
          (if H.side3Cut v ω z₁ ≠ H.side3Cut v ω z₂ then 1 else 0) * H.nonAdjInd z₁ z₂ =
          (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, (if ω u = false then 1 else 0) * H.nonAdjInd u w) +
          (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if ω u = true then 1 else 0) * H.nonAdjInd u w) := by
        rw [← H.union_WASet_WBSet v, sum_inner_union (H.USet v) (H.disjoint_WASet_WBSet v)]
        congr 1
        · refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
          have hwU : w ∉ H.USet v := fun h =>
            Finset.disjoint_left.mp (H.disjoint_USet_WSet v) h (Finset.filter_subset _ _ hw)
          simp only [side3Cut, hu, hwU, ↓reduceIte, decide_eq_true hw]; cases ω u <;> simp
        · refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
          have hwU : w ∉ H.USet v := fun h =>
            Finset.disjoint_left.mp (H.disjoint_USet_WSet v) h (Finset.filter_subset _ _ hw)
          have hwWA : w ∉ H.WASet v := fun h =>
            Finset.disjoint_left.mp (H.disjoint_WASet_WBSet v) h hw
          simp only [side3Cut, hu, hwU, ↓reduceIte, decide_eq_false hwWA]; cases ω u <;> simp
      have hWU_sym : ∑ z₁ ∈ H.WSet v, ∑ z₂ ∈ H.USet v,
          (if H.side3Cut v ω z₁ ≠ H.side3Cut v ω z₂ then 1 else 0) * H.nonAdjInd z₁ z₂ =
          ∑ z₁ ∈ H.USet v, ∑ z₂ ∈ H.WSet v,
            (if H.side3Cut v ω z₁ ≠ H.side3Cut v ω z₂ then 1 else 0) * H.nonAdjInd z₁ z₂ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z₁ _ => Finset.sum_congr rfl fun z₂ _ => by
          rw [H.nonAdjInd_symm z₂ z₁]; cases H.side3Cut v ω z₁ <;> cases H.side3Cut v ω z₂ <;> simp
      linarith
    unfold cCard gRaw qWRaw; linarith
  have hsum_pt := Finset.sum_le_sum (s := Finset.univ) fun ω _ => hpt_rho ω
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_pt
  have hUU_exp : ∑ ω : V → Bool,
      (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u ≠ ω u' then 1 else 0) * H.nonAdjInd u u') =
      (K / 2) * (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.nonAdjInd u u') := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    by_cases hne : u = u'
    · subst hne; simp [H.nonAdjInd_self u]
    · rw [← Finset.sum_mul, sum_bool_neq_eq hne]
  have hUWA_exp : ∑ ω : V → Bool,
      (2 * (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, (if ω u = false then 1 else 0) * H.nonAdjInd u w)) =
      K * (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, H.nonAdjInd u w) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h1 : ∑ u ∈ H.USet v, ∑ ω : V → Bool,
        ∑ w ∈ H.WASet v, (if ω u = false then 1 else 0) * H.nonAdjInd u w =
        (K / 2) * (∑ u ∈ H.USet v, ∑ w ∈ H.WASet v, H.nonAdjInd u w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Finset.sum_mul, sum_bool_eq u false]
    linarith
  have hUWB_exp : ∑ ω : V → Bool,
      (2 * (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if ω u = true then 1 else 0) * H.nonAdjInd u w)) =
      K * (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, H.nonAdjInd u w) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h1 : ∑ u ∈ H.USet v, ∑ ω : V → Bool,
        ∑ w ∈ H.WBSet v, (if ω u = true then 1 else 0) * H.nonAdjInd u w =
        (K / 2) * (∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, H.nonAdjInd u w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Finset.sum_mul, sum_bool_eq u true]
    linarith
  have hUU_val : ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.nonAdjInd u u' =
      ((H.USet v).card : ℝ) * (((H.USet v).card : ℝ) - 1) - 2 * H.cCard v ^ 2 * H.t1Norm v := by
    have htot : ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if u ≠ u' then (1 : ℝ) else 0) =
        ((H.USet v).card : ℝ) * (((H.USet v).card : ℝ) - 1) := by
      have hin : ∀ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if u ≠ u' then (1 : ℝ) else 0) =
          ((H.USet v).card : ℝ) - 1 := by
        intro u hu
        have h1 : ∑ u' ∈ H.USet v, ((if u ≠ u' then (1 : ℝ) else 0) + (if u = u' then 1 else 0)) =
            ((H.USet v).card : ℝ) := by
          have ha : ∀ u' ∈ H.USet v, (if u ≠ u' then (1 : ℝ) else 0) + (if u = u' then 1 else 0) = 1 :=
            fun u' _ => by by_cases h : u = u' <;> simp [h]
          rw [Finset.sum_congr rfl ha, Finset.sum_const, nsmul_eq_mul, mul_one]
        have h2 : ∑ u' ∈ H.USet v, (if u = u' then (1 : ℝ) else 0) = 1 := by
          rw [← Finset.sum_filter]
          have hf : (H.USet v).filter (fun u' => u = u') = {u} := by
            ext u'; simp only [Finset.mem_filter, Finset.mem_singleton]
            exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨h ▸ hu, h.symm⟩⟩
          rw [hf, Finset.sum_singleton]
        rw [Finset.sum_add_distrib, h2] at h1; linarith
      rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
    have hcomm : ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u' u =
        ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u' := Finset.sum_comm
    have hp : ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if u ≠ u' then (1 : ℝ) else 0) =
        (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u') +
        (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u' u) +
        (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.nonAdjInd u u') := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
      by_cases hne : u = u'
      · subst hne; simp [H.arcInd_self u, H.nonAdjInd_self u]
      · simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
        exact (H.arc_add_arc_add_nonAdj hne).symm
    have ht1_eq : H.cCard v ^ 2 * H.t1Norm v = ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u' := by
      unfold t1Norm; exact mul_div_cancel₀ _ hc2_pos.ne'
    linarith
  have hU_le_c : ((H.USet v).card : ℝ) ≤ H.cCard v := by
    unfold cCard; exact_mod_cast Finset.card_le_card (Finset.filter_subset _ (H.CSet v))
  have ha2_bound : H.aNorm v ^ 2 * H.cCard v ^ 2 / 2 ≤
      2 * H.cCard v + (((H.USet v).card : ℝ) * (((H.USet v).card : ℝ) - 1)) / 2 := by
    have hac : H.aNorm v * H.cCard v = ((H.USet v).card : ℝ) := by
      unfold aNorm; exact div_mul_cancel₀ _ hc_pos.ne'
    have hac2 : H.aNorm v ^ 2 * H.cCard v ^ 2 = ((H.USet v).card : ℝ) ^ 2 := by
      rw [← mul_pow, hac]
    nlinarith
  have hK_eq : (Fintype.card (V → Bool) : ℝ) = K := rfl
  have hK_pos : 0 < K := omegaCard_pos
  rw [hUU_exp, hUWA_exp, hUWB_exp, hUU_val, hK_eq] at hsum_pt
  change K * _ ≤ _
  nlinarith [hsum_pt, ha2_bound, H.pivot_UW_nonAdj_id hc_ge1]

private lemma pivot_cut3_tau {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card) :
    ∑ ω : V → Bool, H.tauReal v (H.side3Cut v ω) ≤
      omegaCard V * (H.cCard v ^ 2 * H.xNorm v + H.cCard v ^ 2 * H.t1Norm v / 4 +
        H.cCard v ^ 2 * H.t2Norm v / 2 + H.cCard v ^ 2 * H.m3Norm v) := by
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos (H.cCard_pos hc_ge1)
  let K : ℝ := omegaCard V
  have hpt_tau : ∀ ω : V → Bool, H.tauReal v (H.side3Cut v ω) ≤
      (∑ a₀ ∈ H.ASet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd a₀ u) +
      (∑ u ∈ H.USet v, ∑ b₀ ∈ H.BSet v, (if ω u = true then 1 else 0) * H.arcInd u b₀) +
      (∑ w ∈ H.WSet v, (H.mFn v w : ℝ)) +
      (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u = true ∧ ω u' = false then 1 else 0) * H.arcInd u u') +
      (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, (if ω u = true then 1 else 0) * H.arcInd u w) +
      (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd w u) +
      H.cCard v ^ 2 * H.m3Norm v := by
    intro ω
    have hs3_WA : ∀ w ∈ H.WASet v, H.side3Cut v ω w = true := fun w hw => by
      have hwU : w ∉ H.USet v := fun h =>
        Finset.disjoint_left.mp (H.disjoint_USet_WSet v) h (Finset.filter_subset _ _ hw)
      simp only [side3Cut, hwU, ↓reduceIte, decide_eq_true hw]
    have hs3_WB : ∀ w ∈ H.WBSet v, H.side3Cut v ω w = false := fun w hw => by
      have hwU : w ∉ H.USet v := fun h =>
        Finset.disjoint_left.mp (H.disjoint_USet_WSet v) h (Finset.filter_subset _ _ hw)
      have hwWA : w ∉ H.WASet v := fun h =>
        Finset.disjoint_left.mp (H.disjoint_WASet_WBSet v) h hw
      simp only [side3Cut, hwU, ↓reduceIte, decide_eq_false hwWA]
    rw [H.pivot_exp_tau hc_ge1 (H.side3Cut v ω) hs3_WA hs3_WB]
    have hAU : ∑ a₀ ∈ H.ASet v, ∑ u ∈ H.USet v, (if H.side3Cut v ω u = false then 1 else 0) * H.arcInd a₀ u =
        ∑ a₀ ∈ H.ASet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd a₀ u :=
      Finset.sum_congr rfl fun a₀ _ => Finset.sum_congr rfl fun u hu => by simp only [side3Cut, hu, ↓reduceIte]
    have hUB : ∑ u ∈ H.USet v, ∑ b₀ ∈ H.BSet v, (if H.side3Cut v ω u = true then 1 else 0) * H.arcInd u b₀ =
        ∑ u ∈ H.USet v, ∑ b₀ ∈ H.BSet v, (if ω u = true then 1 else 0) * H.arcInd u b₀ :=
      Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun b₀ _ => by simp only [side3Cut, hu, ↓reduceIte]
    have hUU : ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v,
        (if H.side3Cut v ω u = true ∧ H.side3Cut v ω u' = false then 1 else 0) * H.arcInd u u' =
        ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u = true ∧ ω u' = false then 1 else 0) * H.arcInd u u' :=
      Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => by
        simp only [side3Cut, hu, hu', ↓reduceIte]
    have hUW_le : ∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if H.side3Cut v ω u = true then 1 else 0) * H.arcInd u w ≤
        ∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, (if ω u = true then 1 else 0) * H.arcInd u w := by
      have h1 : ∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if H.side3Cut v ω u = true then 1 else 0) * H.arcInd u w =
          ∑ u ∈ H.USet v, ∑ w ∈ H.WBSet v, (if ω u = true then 1 else 0) * H.arcInd u w :=
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w _ => by simp only [side3Cut, hu, ↓reduceIte]
      rw [h1]
      exact Finset.sum_le_sum fun u _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun w _ _ => mul_nonneg (by split_ifs <;> norm_num) (H.arcInd_nonneg u w))
    have hWU_le : ∑ w ∈ H.WASet v, ∑ u ∈ H.USet v, (if H.side3Cut v ω u = false then 1 else 0) * H.arcInd w u ≤
        ∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd w u := by
      have h1 : ∑ w ∈ H.WASet v, ∑ u ∈ H.USet v, (if H.side3Cut v ω u = false then 1 else 0) * H.arcInd w u =
          ∑ w ∈ H.WASet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd w u :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u hu => by simp only [side3Cut, hu, ↓reduceIte]
      rw [h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun w _ _ => Finset.sum_nonneg fun u _ =>
          mul_nonneg (by split_ifs <;> norm_num) (H.arcInd_nonneg w u))
    linarith
  have hsum_pt := Finset.sum_le_sum (s := Finset.univ) fun ω _ => hpt_tau ω
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_pt
  have hAU_e : ∑ ω : V → Bool,
      (∑ a₀ ∈ H.ASet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd a₀ u) =
      (K / 2) * (∑ u ∈ H.USet v, (H.kFn v u : ℝ)) := by
    rw [Finset.sum_comm]
    have h1 : ∑ a₀ ∈ H.ASet v, ∑ ω : V → Bool,
        ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd a₀ u =
        (K / 2) * (∑ a₀ ∈ H.ASet v, ∑ u ∈ H.USet v, H.arcInd a₀ u) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a₀ _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, sum_bool_eq u false]
    rw [h1, Finset.sum_comm (s := H.ASet v) (t := H.USet v)]
    simp_rw [← H.kFn_eq v]
  have hUB_e : ∑ ω : V → Bool,
      (∑ u ∈ H.USet v, ∑ b₀ ∈ H.BSet v, (if ω u = true then 1 else 0) * H.arcInd u b₀) =
      (K / 2) * (∑ u ∈ H.USet v, (H.lFn v u : ℝ)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm, H.lFn_eq v u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b₀ _ => ?_
    rw [← Finset.sum_mul, sum_bool_eq u true]
  have hUU_e : ∑ ω : V → Bool,
      (∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, (if ω u = true ∧ ω u' = false then 1 else 0) * H.arcInd u u') =
      (K / 4) * (H.cCard v ^ 2 * H.t1Norm v) := by
    have ht1_eq : H.cCard v ^ 2 * H.t1Norm v = ∑ u ∈ H.USet v, ∑ u' ∈ H.USet v, H.arcInd u u' := by
      unfold t1Norm; exact mul_div_cancel₀ _ hc2_pos.ne'
    rw [ht1_eq, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    by_cases hne : u = u'
    · subst hne; simp [H.arcInd_self u]
    · rw [← Finset.sum_mul, sum_bool_pair_eq hne true false]
  have hUW_e : ∑ ω : V → Bool,
      (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, (if ω u = true then 1 else 0) * H.arcInd u w) =
      (K / 2) * (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, sum_bool_eq u true]
  have hWU_e : ∑ ω : V → Bool,
      (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, (if ω u = false then 1 else 0) * H.arcInd w u) =
      (K / 2) * (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, sum_bool_eq u false]
  have hx_eq : H.cCard v ^ 2 * H.xNorm v =
      ((∑ u ∈ H.USet v, (H.kFn v u : ℝ)) + (∑ u ∈ H.USet v, (H.lFn v u : ℝ))) / 2 +
      (∑ w ∈ H.WSet v, (H.mFn v w : ℝ)) := by
    unfold xNorm
    rw [mul_div_cancel₀ _ hc2_pos.ne', ← Finset.sum_div, Finset.sum_add_distrib]
  have ht2_eq : H.cCard v ^ 2 * H.t2Norm v =
      (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
      (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u) := by
    unfold t2Norm; exact mul_div_cancel₀ _ hc2_pos.ne'
  have hK_eq : (Fintype.card (V → Bool) : ℝ) = K := rfl
  rw [hAU_e, hUB_e, hUU_e, hUW_e, hWU_e, hK_eq] at hsum_pt
  have hrhs_eq : K * (H.cCard v ^ 2 * H.xNorm v + H.cCard v ^ 2 * H.t1Norm v / 4 +
      H.cCard v ^ 2 * H.t2Norm v / 2 + H.cCard v ^ 2 * H.m3Norm v) =
      (K / 2) * (∑ u ∈ H.USet v, (H.kFn v u : ℝ)) +
      (K / 2) * (∑ u ∈ H.USet v, (H.lFn v u : ℝ)) +
      K * (∑ w ∈ H.WSet v, (H.mFn v w : ℝ)) +
      (K / 4) * (H.cCard v ^ 2 * H.t1Norm v) +
      (K / 2) * (∑ u ∈ H.USet v, ∑ w ∈ H.WSet v, H.arcInd u w) +
      (K / 2) * (∑ w ∈ H.WSet v, ∑ u ∈ H.USet v, H.arcInd w u) +
      K * (H.cCard v ^ 2 * H.m3Norm v) := by
    rw [hx_eq, ht2_eq]; ring
  change _ ≤ K * _
  linarith [hsum_pt, hrhs_eq]


private lemma pivot_cut3_83 {v : V} (hc_ge1 : 1 ≤ (H.CSet v).card)
    (hex_good : ∀ (side : V → Bool), 83 * H.ordRhoReal v side < 200 * H.tauReal v side) :
    H.gNorm v - (100 / 83) * H.xNorm v + H.qWNorm v <
      (133 / 166) * H.t1Norm v + (183 / 166) * H.t2Norm v + (100 / 83) * H.m3Norm v -
        H.aNorm v ^ 2 / 4 - H.aNorm v * (1 - H.aNorm v) / 2 := by
  have hc_pos := H.cCard_pos hc_ge1
  have hc2_pos : 0 < H.cCard v ^ 2 := sq_pos_of_pos hc_pos
  let K : ℝ := omegaCard V
  have hK_pos : 0 < K := omegaCard_pos
  have _ : Nonempty (V → Bool) := ⟨fun _ => false⟩
  have hsum_bad3 : 83 * (∑ ω : V → Bool, H.ordRhoReal v (H.side3Cut v ω)) <
      200 * (∑ ω : V → Bool, H.tauReal v (H.side3Cut v ω)) := by
    have hlt : ∀ ω ∈ (Finset.univ : Finset (V → Bool)),
        83 * H.ordRhoReal v (H.side3Cut v ω) - 200 * H.tauReal v (H.side3Cut v ω) < 0 :=
      fun ω _ => sub_neg.mpr (hex_good (H.side3Cut v ω))
    have hneg := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
    simp only [Finset.sum_const_zero, Finset.sum_sub_distrib, ← Finset.mul_sum] at hneg
    linarith
  have hrho3 := H.pivot_cut3_rho_83 hc_ge1
  have htau3 := H.pivot_cut3_tau hc_ge1
  have ha1a_eq : H.aNorm v * (1 - H.aNorm v) * H.cCard v ^ 2 =
      ((H.USet v).card : ℝ) * ((H.WSet v).card : ℝ) := by
    rw [H.one_sub_aNorm hc_ge1]; unfold aNorm; field_simp [hc_pos.ne']
  have hg_eq : H.gNorm v * H.cCard v ^ 2 = H.gRaw v := by unfold gNorm; exact div_mul_cancel₀ _ hc2_pos.ne'
  have hq_eq : H.qWNorm v * H.cCard v ^ 2 = H.qWRaw v := by unfold qWNorm; exact div_mul_cancel₀ _ hc2_pos.ne'
  rw [← ha1a_eq, ← hg_eq, ← hq_eq] at hrho3
  have hK_ineq : K * (H.cCard v ^ 2 * (166 * (H.gNorm v - (100 / 83) * H.xNorm v + H.qWNorm v))) <
      K * (H.cCard v ^ 2 * (166 * ((133 / 166) * H.t1Norm v + (183 / 166) * H.t2Norm v +
        (100 / 83) * H.m3Norm v - H.aNorm v ^ 2 / 4 - H.aNorm v * (1 - H.aNorm v) / 2))) := by
    change K * _ ≤ _ at hrho3
    change _ ≤ K * _ at htau3
    linarith [hsum_bad3, hrho3, htau3]
  have h1 := lt_of_mul_lt_mul_left hK_ineq hK_pos.le
  have h2 := lt_of_mul_lt_mul_left h1 hc2_pos.le
  linarith

private lemma pivot_contradiction_83 (hH : H.TriangleFree) (v : V)
    (hc_ge1 : 1 ≤ (H.CSet v).card)
    (hpivot : (83 / 80 : ℝ) * ((H.CSet v).card : ℝ) ^ 2 +
        (1059 / 680 : ℝ) * (∑ u ∈ H.CSet v, ∑ w ∈ H.CSet v, H.arcInd u w) <
      (∑ a ∈ H.ASet v, ∑ b ∈ H.BSet v, H.nonAdjInd a b))
    (hex_good : ∀ (side : V → Bool), 83 * H.ordRhoReal v side < 200 * H.tauReal v side) :
    False := by
  have hc2_nn : 0 ≤ H.cCard v ^ 2 := sq_nonneg _
  have ht1_nn : 0 ≤ H.t1Norm v :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => H.arcInd_nonneg _ _) hc2_nn
  have hm3_nn : 0 ≤ H.m3Norm v :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => H.arcInd_nonneg _ _) hc2_nn
  exact step4_final_contradiction_83
    (H.pivot_step1_norm_83 hc_ge1 hpivot)
    (H.pivot_step3_83 hH hc_ge1)
    (H.pivot_cut3_83 hc_ge1 hex_good)
    ht1_nn
    (H.pivot_t2_le hc_ge1)
    hm3_nn
    (H.pivot_m3_le_t3 hc_ge1)

/-- **CSS feedback arc set bound**
Every finite simple `C₃`-free oriented graph `G` admits a feedback arc set `F` and an injective
topological ranking `rank : W → ℕ` such that `200 * F.card ≤ 83 * G.ordNonEdges`
(equivalently `100 * β(G) ≤ 83 * γ(G)`). -/
theorem exists_feedback_200_card_le_83_ordNonEdges :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : OrientedGraph W) [DecidableRel G.adj],
      G.TriangleFree →
      ∃ (F : Finset (W × W)) (rank : W → ℕ),
        Function.Injective rank ∧
        (∀ u w : W, G.adj u w → (u, w) ∉ F → rank w < rank u) ∧
        200 * F.card ≤ 83 * G.ordNonEdges := by
  suffices hmain : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : OrientedGraph W) [DecidableRel G.adj],
      Fintype.card W = n → G.TriangleFree →
      ∃ (F : Finset (W × W)) (rank : W → ℕ),
        Function.Injective rank ∧
        (∀ u w : W, G.adj u w → (u, w) ∉ F → rank w < rank u) ∧
        200 * F.card ≤ 83 * G.ordNonEdges by
    intro W _ _ G _ hG
    exact hmain (Fintype.card W) G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro W _ _ G _ hn hG
    by_cases hne : Nonempty W
    · by_cases hex_good : ∃ (v : W) (side : W → Bool), 200 * G.tauReal v side ≤ 83 * G.ordRhoReal v side
      · rcases hex_good with ⟨v, side, hgood⟩
        exact G.exists_feedback_of_good_cut hG v side
          (fun S hS => ih S.card (hn ▸ hS) (G.induce S) (Fintype.card_coe S) (G.triangleFree_induce hG S))
          hgood
      · exfalso
        push Not at hex_good
        obtain ⟨v, hc_ge1, hpivot⟩ := G.exists_pivot_vertex_83 hG hex_good
        exact G.pivot_contradiction_83 hG v hc_ge1 hpivot (hex_good v)
    · rw [not_nonempty_iff] at hne
      refine ⟨∅, isEmptyElim, fun x => isEmptyElim x, fun x => isEmptyElim x, ?_⟩
      simp

end CSS83

/-- **Out-degree corollary (`α_CSS = 83/100`)**:
In ANY finite nonempty `C₃`-free oriented graph `H` where every vertex has out-degree `≥ d`,
`100 * (d * (d + 1)) ≤ 83 * H.ordNonEdges` (equivalently `δ⁺(H)^2 ≤ (83/50) γ(H) = 1.66 γ(H)`). -/
theorem hundred_outDeg_sq_le_83_ordNonEdges {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : OrientedGraph V) [DecidableRel H.adj] (hH : H.TriangleFree)
    {d : ℕ} (hdeg : ∀ u : V, d ≤ H.toDigraph.outDeg u) :
    100 * (d * (d + 1)) ≤ 83 * H.ordNonEdges := by
  obtain ⟨F, rank, hinj, hdag, hcard⟩ := H.exists_feedback_200_card_le_83_ordNonEdges hH
  have hfb := deg_sq_le_two_card_feedback d H F rank hinj hdag hdeg
  omega

/-- Every finite nonempty `C₃`-free oriented graph `H` has a vertex `w` satisfying
`100 * (outDeg H w * (outDeg H w + 1)) ≤ 83 * H.ordNonEdges`. -/
theorem exists_hundred_outDeg_sq_le_83_ordNonEdges {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : OrientedGraph V) [DecidableRel H.adj] (hH : H.TriangleFree) :
    ∃ w : V, 100 * (H.toDigraph.outDeg w * (H.toDigraph.outDeg w + 1)) ≤ 83 * H.ordNonEdges := by
  obtain ⟨w, _, hw_min⟩ :=
    Finset.exists_min_image Finset.univ (H.toDigraph.outDeg) Finset.univ_nonempty
  exact ⟨w, H.hundred_outDeg_sq_le_83_ordNonEdges hH (fun u => hw_min u (Finset.mem_univ u))⟩

end OrientedGraph

/-- **Feedback arc set bound for a 3-free digraph**
Every finite simple digraph `G` with no directed cycle of length `≤ 3` (`¬ G.HasCycleLe3`) admits
a feedback arc set `F` and an injective topological ranking `rank : V → ℕ` such that
`200 * F.card ≤ 83 * G.ordNonEdges` (equivalently `100 * β(G) ≤ 83 * γ(G)`). -/
theorem Digraph.exists_feedback_200_card_le_83_ordNonEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : Digraph V) [dG : DecidableRel G.adj] (h3free : ¬ G.HasCycleLe3) :
    ∃ (F : Finset (V × V)) (rank : V → ℕ),
      Function.Injective rank ∧
      (∀ u w : V, G.adj u w → (u, w) ∉ F → rank w < rank u) ∧
      200 * F.card ≤ 83 * G.ordNonEdges := by
  have hnodigon : ¬ G.HasDigon := fun hd => h3free (Or.inl hd)
  have hnotri : ¬ G.HasDirTriangle := fun ht => h3free (Or.inr ht)
  let H : OrientedGraph V := G.toOrientedOfNotHasDigon hnodigon
  let _ : DecidableRel H.adj := dG
  exact H.exists_feedback_200_card_le_83_ordNonEdges hnotri

end CaccettaHaggkvist
