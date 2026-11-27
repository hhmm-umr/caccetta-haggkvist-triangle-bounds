module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical
public import CaccettaHaggkvist.WeightBridge
public import CaccettaHaggkvist.FlagCert
public import CaccettaHaggkvist.CSS
public import CaccettaHaggkvist.CSS56
public import CaccettaHaggkvist.CSS83

/-!
# Extremal `ε`-Regularization, Generalized Induction, Pointwise CSS, & Two-Endpoint Interval Bridge

This module formalizes Theorems B1, C1, C2, and Section 5 of `stage1_blueprint.md` in Lean 4 with
zero limits, zero measure theory, and zero `O(1/n)` finite-graph loss:

1. **Theorem B1 (`exists_eps_extremal_regular_orientedGraph`)**:
   Defines `c3FreeRatios : Set ℝ` and its supremum `cStar := sSup c3FreeRatios`. For any `ε > 0`,
   constructs a finite nonempty `C₃`-free `c₀`-out-regular oriented graph `G₀ : OrientedGraph (Fin n)`
   satisfying `cStar - ε < c₀ ≤ cStar` and hereditary out-neighborhood bound `≤ (c₀ + ε) * |U|`.
2. **Theorem C1 (`indWeight_ge_neg_eps_of_nonempty`, `indWeight_ge_neg_eps_of_sink`)**:
   Pointwise generalized induction bound `s*(v) + c₀ * F₀(v) - c₀ ≥ -ε` on `G₀`, holding even when
   non-adjacent tuple coordinates `v_i = v_j` collide!
3. **Theorem C2 (`cssWeight_nonneg_of_nonempty`, `cssWeight_nonneg_of_sink`)**:
   Pointwise rational-linearized Chudnovsky–Seymour–Sullivan bound (`α_CSS = 1`, zero `√`, zero
   `-ε` loss!): `chiVal(v) + 2 * r * s*(v) + (r^2 - 2 * c₀ * r) ≥ 0` on `G₀`!
4. **Section 5 Two-Endpoint Affine Interval Bridge (`hasCycleLe3_of_interval_certificate`)**:
   Verifying strict negativity `≤ -δ < 0` at BOTH `c_low` and `c_high` (where `cStar ≤ c_high` is
   known) proves `cStar < c_low` — including the exact boundary case `cStar = c_low`!
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

/-! ## Section 1: Global Extremal Ratio `cStar` & Theorem B1 (`ε`-Extremal Out-Regular `G₀`) -/

/-- Set of achievable minimum out-degree ratios across all finite nonempty `C₃`-free oriented graphs. -/
def c3FreeRatios : Set ℝ :=
  {r : ℝ | ∃ (n : ℕ) (_ : 0 < n) (H : OrientedGraph (Fin n)) (dH : DecidableRel H.adj),
    H.TriangleFree ∧
    ∀ u : Fin n, r * (n : ℝ) ≤ (@Digraph.outDeg (Fin n) _ H.toDigraph dH u : ℝ)}

lemma zero_mem_c3FreeRatios : (0 : ℝ) ∈ c3FreeRatios := by
  let H : OrientedGraph (Fin 1) :=
    { adj := fun _ _ => False
      loopless := fun _ h => h
      asymm := fun _ _ h => h.elim }
  have dH : DecidableRel H.adj := fun _ _ => isFalse id
  refine ⟨1, Nat.one_pos, H, dH, ?_, ?_⟩
  · rintro ⟨_, _, _, h, _, _⟩; exact h
  · intro u; simp

lemma c3FreeRatios_nonempty : c3FreeRatios.Nonempty :=
  ⟨0, zero_mem_c3FreeRatios⟩

lemma le_one_of_mem_c3FreeRatios {r : ℝ} (hr : r ∈ c3FreeRatios) : r ≤ 1 := by
  rcases hr with ⟨n, hn, H, dH, _, hdeg⟩
  let u₀ : Fin n := ⟨0, hn⟩
  have hlt : @Digraph.outDeg (Fin n) _ H.toDigraph dH u₀ < n := by
    calc @Digraph.outDeg (Fin n) _ H.toDigraph dH u₀
        < (insert u₀ (@Digraph.outSet (Fin n) _ H.toDigraph dH u₀)).card := by
          rw [Finset.card_insert_of_notMem (@Digraph.notMem_outSet_self (Fin n) _ H.toDigraph dH u₀)]
          dsimp [Digraph.outDeg]
          omega
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hreal : (@Digraph.outDeg (Fin n) _ H.toDigraph dH u₀ : ℝ) < (n : ℝ) := by exact_mod_cast hlt
  have hge := hdeg u₀
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  nlinarith

lemma bddAbove_c3FreeRatios : BddAbove c3FreeRatios :=
  ⟨1, fun _ hr => le_one_of_mem_c3FreeRatios hr⟩

/-- The global supremum `c* = sup { δ⁺(H)/|V(H)| : H finite nonempty C₃-free oriented }`. -/
noncomputable def cStar : ℝ := sSup c3FreeRatios

/-- Any finite nonempty `C₃`-free oriented graph `G` with `∀ u, r * |V| ≤ outDeg u` puts
`r ∈ c3FreeRatios`, hence `r ≤ cStar`. -/
lemma mem_c3FreeRatios_of_orientedGraph {V : Type u} [Fintype V] [Nonempty V]
    (G : OrientedGraph V) [dG : DecidableRel G.adj] (hG : G.TriangleFree)
    {r : ℝ} (hdeg : ∀ u : V, r * (Fintype.card V : ℝ) ≤ (G.toDigraph.outDeg u : ℝ)) :
    r ∈ c3FreeRatios := by
  let n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let H : OrientedGraph (Fin n) := G.relabel e
  let dH : DecidableRel H.adj := fun i j => dG (e i) (e j)
  have hH_tri : H.TriangleFree := G.triangleFree_pullback hG e
  refine ⟨n, hn, H, dH, hH_tri, ?_⟩
  intro i
  have hout : @Digraph.outDeg (Fin n) _ H.toDigraph dH i = G.toDigraph.outDeg (e i) := by
    have hmap : (@Digraph.outSet (Fin n) _ H.toDigraph dH i).map e.toEmbedding =
        G.toDigraph.outSet (e i) := by
      ext v
      simp only [Finset.mem_map, Equiv.toEmbedding_apply, Digraph.mem_outSet]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hj; exact ⟨e.symm v, by simpa [H, OrientedGraph.relabel, OrientedGraph.pullback] using hj,
          e.apply_symm_apply v⟩
    dsimp [Digraph.outDeg]
    rw [← hmap, Finset.card_map]
  rw [hout]
  exact hdeg (e i)

lemma le_cStar_of_orientedGraph {V : Type u} [Fintype V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj] (hG : G.TriangleFree)
    {r : ℝ} (hdeg : ∀ u : V, r * (Fintype.card V : ℝ) ≤ (G.toDigraph.outDeg u : ℝ)) :
    r ≤ cStar :=
  le_csSup bddAbove_c3FreeRatios (mem_c3FreeRatios_of_orientedGraph G hG hdeg)

/-- Every nonempty induced subgraph of a `C₃`-free oriented graph has a vertex with internal
out-degree `≤ cStar * |U|`. -/
lemma OrientedGraph.exists_induce_outDeg_le_cStar {V : Type u} [Fintype V] [DecidableEq V]
    (G : OrientedGraph V) [DecidableRel G.adj] (hG : G.TriangleFree)
    {U : Finset V} (hU : U.Nonempty) :
    ∃ w ∈ U, ((U ∩ G.toDigraph.outSet w).card : ℝ) ≤ cStar * (U.card : ℝ) := by
  have _ : Nonempty {z : V // z ∈ U} := Finset.Nonempty.to_subtype hU
  obtain ⟨w, _, hw_min⟩ :=
    Finset.exists_min_image Finset.univ ((G.induce U).toDigraph.outDeg) Finset.univ_nonempty
  let d_min : ℕ := (G.induce U).toDigraph.outDeg w
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have hdeg_all : ∀ x : {z : V // z ∈ U},
      ((d_min : ℝ) / (U.card : ℝ)) * (Fintype.card {z : V // z ∈ U} : ℝ) ≤
        ((G.induce U).toDigraph.outDeg x : ℝ) := by
    intro x
    rw [Fintype.card_coe U, div_mul_cancel₀ _ hU_pos.ne']
    exact_mod_cast hw_min x (Finset.mem_univ x)
  have hle : (d_min : ℝ) / (U.card : ℝ) ≤ cStar :=
    le_cStar_of_orientedGraph (G.induce U) (G.triangleFree_induce hG U) hdeg_all
  have hmul := mul_le_mul_of_nonneg_right hle hU_pos.le
  rw [div_mul_cancel₀ _ hU_pos.ne'] at hmul
  refine ⟨w.1, w.2, ?_⟩
  have hout := G.outDeg_induce U w
  dsimp [d_min] at hmul
  rwa [hout] at hmul

/-- **Theorem B1 (`ε`-Extremal Out-Regular Finite Graph)**:
For any `ε > 0`, there exist `n ≥ 1`, `c₀ ∈ (cStar - ε, cStar]`, and a `C₃`-free oriented graph
`G₀ : OrientedGraph (Fin n)` in which EVERY vertex `u` has exact out-weight `c₀` under
`unifWeight (Fin n)`, and every nonempty `U ⊆ Fin n` has `w ∈ U` with internal out-degree
`≤ (c₀ + ε) * |U|`. -/
theorem exists_eps_extremal_regular_orientedGraph {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (c₀ : ℝ) (G₀ : OrientedGraph (Fin n)) (dG₀ : DecidableRel G₀.adj),
      cStar - ε < c₀ ∧ c₀ ≤ cStar ∧ G₀.TriangleFree ∧
      (∀ u : Fin n, @Digraph.outWeight (Fin n) _ G₀.toDigraph dG₀ (unifWeight (Fin n)) u = c₀) ∧
      (∀ U : Finset (Fin n), U.Nonempty →
        ∃ w ∈ U, ((U ∩ @Digraph.outSet (Fin n) _ G₀.toDigraph dG₀ w).card : ℝ) ≤
          (c₀ + ε) * (U.card : ℝ)) := by
  have hlt_sup : cStar - ε < sSup c3FreeRatios := by
    dsimp [cStar]; linarith
  obtain ⟨r, hr_mem, hr_gt⟩ := exists_lt_of_lt_csSup c3FreeRatios_nonempty hlt_sup
  rcases hr_mem with ⟨n, hn, H₁, dH₁, hH₁_tri, hH₁_deg⟩
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let d₀ : ℕ := Finset.univ.inf' Finset.univ_nonempty
    (fun u : Fin n => @Digraph.outDeg (Fin n) _ H₁.toDigraph dH₁ u)
  have hd₀_le : ∀ u : Fin n, d₀ ≤ (@Digraph.outSet (Fin n) _ H₁.toDigraph dH₁ u).card :=
    fun u => Finset.inf'_le _ (Finset.mem_univ u)
  choose S hS_sub hS_card using fun u => Finset.exists_subset_card_eq (hd₀_le u)
  let G₀ : OrientedGraph (Fin n) :=
    { adj := fun u v => v ∈ S u
      loopless := fun u hu => H₁.loopless u ((@Digraph.mem_outSet (Fin n) _ H₁.toDigraph dH₁).mp (hS_sub u hu))
      asymm := fun u v huv hvu =>
        H₁.asymm u v ((@Digraph.mem_outSet (Fin n) _ H₁.toDigraph dH₁).mp (hS_sub u huv))
          ((@Digraph.mem_outSet (Fin n) _ H₁.toDigraph dH₁).mp (hS_sub v hvu)) }
  let dG₀ : DecidableRel G₀.adj := fun u v => Finset.decidableMem v (S u)
  have hG₀_tri : G₀.TriangleFree := by
    rintro ⟨u, v, w, huv, hvw, hwu⟩
    exact hH₁_tri ⟨u, v, w,
      (@Digraph.mem_outSet (Fin n) _ H₁.toDigraph dH₁).mp (hS_sub u huv),
      (@Digraph.mem_outSet (Fin n) _ H₁.toDigraph dH₁).mp (hS_sub v hvw),
      (@Digraph.mem_outSet (Fin n) _ H₁.toDigraph dH₁).mp (hS_sub w hwu)⟩
  have hout_eq : ∀ u : Fin n, @Digraph.outDeg (Fin n) _ G₀.toDigraph dG₀ u = d₀ := by
    intro u
    have hset : @Digraph.outSet (Fin n) _ G₀.toDigraph dG₀ u = S u := by
      ext v; simp [Digraph.outSet, G₀]
    dsimp [Digraph.outDeg]
    rw [hset, hS_card u]
  let c₀ : ℝ := (d₀ : ℝ) / (n : ℝ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr_le_c₀ : r ≤ c₀ := by
    obtain ⟨u_min, _, hu_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun u : Fin n => @Digraph.outDeg (Fin n) _ H₁.toDigraph dH₁ u)
    have h1 := hH₁_deg u_min
    have hd_eq : (@Digraph.outDeg (Fin n) _ H₁.toDigraph dH₁ u_min : ℝ) = (d₀ : ℝ) := by
      exact_mod_cast hu_eq.symm
    rw [hd_eq] at h1
    exact (le_div_iff₀ hn_pos).mpr h1
  have hc₀_le_cStar : c₀ ≤ cStar := by
    apply @le_cStar_of_orientedGraph (Fin n) _ _ G₀ dG₀ hG₀_tri c₀
    intro u
    rw [Fintype.card_fin, hout_eq u]
    dsimp [c₀]
    rw [div_mul_cancel₀ _ hn_pos.ne']
  have hc₀_gt : cStar - ε < c₀ := lt_of_lt_of_le hr_gt hr_le_c₀
  refine ⟨n, hn, c₀, G₀, dG₀, hc₀_gt, hc₀_le_cStar, hG₀_tri, ?_, ?_⟩
  · intro u
    rw [@Digraph.outWeight_unifWeight (Fin n) _ G₀.toDigraph dG₀ u, Fintype.card_fin, hout_eq u]
  · intro U hU
    obtain ⟨w, hwU, hw_le⟩ := @OrientedGraph.exists_induce_outDeg_le_cStar (Fin n) _ _ G₀ dG₀ hG₀_tri U hU
    refine ⟨w, hwU, ?_⟩
    have hcStar_le : cStar ≤ c₀ + ε := by linarith
    have hU_nn : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg U.card
    nlinarith

/-! ## Section 2: Theorem C1 (Pointwise Generalized Induction on `G₀`) -/

/-- Common out-neighborhood `U(v) = {x | ∀ i, v_i → x}` of a `k`-tuple `v` (duplicate-safe!). -/
def commonOutSet {V : Type u} [Fintype V] (G : OrientedGraph V) [DecidableRel G.adj]
    {k : ℕ} (v : Fin k → V) : Finset V :=
  Finset.univ.filter fun x => ∀ i : Fin k, G.adj (v i) x

/-- Source-free non-common vertices `Src*(v) = {x | (∀ i, ¬ x → v_i) ∧ ¬ (∀ i, v_i → x)}`. -/
def srcStarSet {V : Type u} [Fintype V] (G : OrientedGraph V) [DecidableRel G.adj]
    {k : ℕ} (v : Fin k → V) : Finset V :=
  Finset.univ.filter fun x => (∀ i : Fin k, ¬ G.adj x (v i)) ∧ ¬ (∀ i : Fin k, G.adj (v i) x)

/-- **Theorem C1 (Conditional / Nonempty `U(v)` Branch)**:
Whenever `(commonOutSet G₀ v).Nonempty`, `(srcStarSet.card + c₀ * commonOutSet.card) / n - c₀ ≥ -ε`. -/
theorem ind_ineq_of_commonOut_nonempty {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (hhered : ∀ U : Finset (Fin n), U.Nonempty →
      ∃ w ∈ U, ((U ∩ G₀.toDigraph.outSet w).card : ℝ) ≤ (c₀ + ε) * (U.card : ℝ))
    (v : Fin k → Fin n) (hU : (commonOutSet G₀ v).Nonempty) :
    -ε ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) +
      c₀ * (((commonOutSet G₀ v).card : ℝ) / (n : ℝ)) - c₀ := by
  let U := commonOutSet G₀ v
  obtain ⟨w, hwU, hw_int⟩ := hhered U hU
  have hw_all : ∀ i : Fin k, G₀.adj (v i) w := (Finset.mem_filter.mp hwU).2
  have hsub : G₀.toDigraph.outSet w \ U ⊆ srcStarSet G₀ v := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_out, hx_notU⟩
    rw [Digraph.mem_outSet] at hx_out
    simp only [U, commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx_notU
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hx_notU⟩⟩
    intro i hxi
    exact hG₀ ⟨v i, w, x, hw_all i, hx_out, hxi⟩
  have hsdiff_card :
      (G₀.toDigraph.outSet w).card ≤ (srcStarSet G₀ v).card + (U ∩ G₀.toDigraph.outSet w).card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_inter (G₀.toDigraph.outSet w) U
    rw [Finset.inter_comm] at h2
    omega
  have hreal_card : (G₀.toDigraph.outDeg w : ℝ) ≤
      ((srcStarSet G₀ v).card : ℝ) + ((U ∩ G₀.toDigraph.outSet w).card : ℝ) := by
    exact_mod_cast hsdiff_card
  have hU_le_n : (U.card : ℝ) ≤ (n : ℝ) := by
    have hnat : U.card ≤ Fintype.card (Fin n) := Finset.card_le_univ U
    rw [Fintype.card_fin] at hnat
    exact_mod_cast hnat
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have heps_ratio : ε * ((U.card : ℝ) / (n : ℝ)) ≤ ε := by
    have hle1 : (U.card : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn_pos).mpr hU_le_n
    nlinarith
  have hdiv : c₀ ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) +
      (c₀ + ε) * (((U.card : ℝ) / (n : ℝ))) := by
    have hsum : c₀ * (n : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (c₀ + ε) * (U.card : ℝ) := by
      linarith [hreg w, hreal_card, hw_int]
    calc c₀ = (c₀ * (n : ℝ)) / (n : ℝ) := by field_simp [hn_pos.ne']
      _ ≤ (((srcStarSet G₀ v).card : ℝ) + (c₀ + ε) * (U.card : ℝ)) / (n : ℝ) :=
          div_le_div_of_nonneg_right hsum hn_pos.le
      _ = ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) + (c₀ + ε) * ((U.card : ℝ) / (n : ℝ)) := by ring
  linarith

/-- **Theorem C1 (Universal Sink Unconditional Branch)**:
If `r ∈ Fin k` is a universal sink (`∀ i ≠ r, v_i → v_r`), the induction inequality holds for
EVERY `v` (even when `commonOutSet G₀ v = ∅` and even when roots collide!). -/
theorem ind_ineq_of_universal_sink {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (hhered : ∀ U : Finset (Fin n), U.Nonempty →
      ∃ w ∈ U, ((U ∩ G₀.toDigraph.outSet w).card : ℝ) ≤ (c₀ + ε) * (U.card : ℝ))
    (v : Fin k → Fin n) (r : Fin k) (hsink : ∀ i : Fin k, i ≠ r → G₀.adj (v i) (v r)) :
    -ε ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) +
      c₀ * (((commonOutSet G₀ v).card : ℝ) / (n : ℝ)) - c₀ := by
  rcases (commonOutSet G₀ v).eq_empty_or_nonempty with h_emp | h_ne
  · have hsub : G₀.toDigraph.outSet (v r) ⊆ srcStarSet G₀ v := by
      intro x hx
      rw [Digraph.mem_outSet] at hx
      have hnotU : x ∉ commonOutSet G₀ v := by rw [h_emp]; simp
      simp only [commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnotU
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hnotU⟩⟩
      intro i hxi
      by_cases hir : i = r
      · rw [hir] at hxi; exact G₀.asymm (v r) x hx hxi
      · exact hG₀ ⟨v i, v r, x, hsink i hir, hx, hxi⟩
    have hcard_ge : (G₀.toDigraph.outDeg (v r) : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hs_ge : c₀ ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]
      linarith [hreg (v r), hcard_ge]
    rw [h_emp]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, mul_zero, add_zero]
    linarith
  · exact ind_ineq_of_commonOut_nonempty hn G₀ hG₀ hε hreg hhered v h_ne

/-! ## Section 3: Theorem C2 (Pointwise Rational CSS with `α_CSS = 1`, ZERO `ε` Loss!) -/

/-- Ordered pairs `(x, y)` in `commonOutSet G₀ v × commonOutSet G₀ v` that are non-adjacent in `G₀`
(including diagonal pairs `(x, x)`!). -/
def chiPairSet {V : Type u} [Fintype V] (G : OrientedGraph V) [DecidableRel G.adj]
    {k : ℕ} (v : Fin k → V) : Finset (V × V) :=
  Finset.univ.filter fun p : V × V =>
    (∀ i : Fin k, G.adj (v i) p.1) ∧ (∀ i : Fin k, G.adj (v i) p.2) ∧
      ¬ G.adj p.1 p.2 ∧ ¬ G.adj p.2 p.1

/-- **Theorem C2 (Conditional / Nonempty `U(v)` Branch, `α_CSS = 1`, exact `≥ 0`!)**:
Whenever `(commonOutSet G₀ v).Nonempty`, for ANY `r ≥ 0`,
`chiPairSet.card / n² + 2 * r * (srcStarSet.card / n) + (r² - 2 * c₀ * r) ≥ 0`! -/
theorem css_ineq_of_commonOut_nonempty {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (hU : (commonOutSet G₀ v).Nonempty) :
    0 ≤ ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  let U := commonOutSet G₀ v
  have _ : Nonempty {z : Fin n // z ∈ U} := Finset.Nonempty.to_subtype hU
  obtain ⟨w, hw_sq⟩ := (G₀.induce U).exists_outDeg_sq_le_ordNonEdges (G₀.triangleFree_induce hG₀ U)
  -- Embed non-edges of G₀[U] into chiPairSet G₀ v
  let embU : ({z : Fin n // z ∈ U} × {z : Fin n // z ∈ U}) ↪ Fin n × Fin n :=
    ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
      rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
      injection h with ha hb; subst ha; subst hb; rfl⟩
  have hord_le_chi : (G₀.induce U).ordNonEdges ≤ (chiPairSet G₀ v).card := by
    let raw := Finset.univ.filter fun p : {z : Fin n // z ∈ U} × {z : Fin n // z ∈ U} =>
      p.1 ≠ p.2 ∧ ¬ (G₀.induce U).adj p.1 p.2 ∧ ¬ (G₀.induce U).adj p.2 p.1
    have hsub : raw.map embU ⊆ chiPairSet G₀ v := by
      intro p hp
      rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy, rfl⟩
      have hxU := (Finset.mem_filter.mp hx).2
      have hyU := (Finset.mem_filter.mp hy).2
      have hne := (Finset.mem_filter.mp hxy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hxU, hyU, hne.2.1, hne.2.2⟩⟩
    calc (G₀.induce U).ordNonEdges = (raw.map embU).card := (Finset.card_map embU).symm
      _ ≤ (chiPairSet G₀ v).card := Finset.card_le_card hsub
  have hw_all : ∀ i : Fin k, G₀.adj (v i) w.1 := (Finset.mem_filter.mp w.2).2
  have hsub_src : G₀.toDigraph.outSet w.1 \ U ⊆ srcStarSet G₀ v := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_out, hx_notU⟩
    rw [Digraph.mem_outSet] at hx_out
    simp only [U, commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx_notU
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hx_notU⟩⟩
    intro i hxi
    exact hG₀ ⟨v i, w.1, x, hw_all i, hx_out, hxi⟩
  let d_U : ℕ := (G₀.induce U).toDigraph.outDeg w
  have hd_U_eq : d_U = (U ∩ G₀.toDigraph.outSet w.1).card := G₀.outDeg_induce U w
  have hsdiff_card : (G₀.toDigraph.outSet w.1).card ≤ (srcStarSet G₀ v).card + d_U := by
    have h1 := Finset.card_le_card hsub_src
    have h2 := Finset.card_sdiff_add_card_inter (G₀.toDigraph.outSet w.1) U
    rw [Finset.inter_comm, ← hd_U_eq] at h2
    omega
  have hd_sq_chi : (d_U : ℝ) ^ 2 ≤ ((chiPairSet G₀ v).card : ℝ) := by
    have hnat : d_U * d_U ≤ (chiPairSet G₀ v).card := by
      have h1 : d_U * d_U ≤ d_U * (d_U + 1) := Nat.mul_le_mul_left d_U (Nat.le_succ d_U)
      exact le_trans h1 (le_trans hw_sq hord_le_chi)
    have hcast : ((d_U * d_U : ℕ) : ℝ) ≤ ((chiPairSet G₀ v).card : ℝ) := by exact_mod_cast hnat
    simpa [sq] using hcast
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  let s_val : ℝ := ((srcStarSet G₀ v).card : ℝ) / (n : ℝ)
  let chi_val : ℝ := ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)
  have hc₀_sub : c₀ - s_val ≤ (d_U : ℝ) / (n : ℝ) := by
    dsimp [s_val]
    have hreal : c₀ * (n : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (d_U : ℝ) := by
      have hcast : (G₀.toDigraph.outDeg w.1 : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (d_U : ℝ) := by
        exact_mod_cast hsdiff_card
      linarith [hreg w.1, hcast]
    calc c₀ - ((srcStarSet G₀ v).card : ℝ) / (n : ℝ)
        = (c₀ * (n : ℝ) - ((srcStarSet G₀ v).card : ℝ)) / (n : ℝ) := by field_simp [hn_pos.ne']
      _ ≤ (d_U : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right (by linarith) hn_pos.le
  have hchi_ge_sq : ((d_U : ℝ) / (n : ℝ)) ^ 2 ≤ chi_val := by
    dsimp [chi_val]
    rw [div_pow]
    exact div_le_div_of_nonneg_right hd_sq_chi (sq_nonneg (n : ℝ))
  have hchi_nn : 0 ≤ chi_val := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  by_cases hcs : c₀ - s_val ≤ 0
  · nlinarith [sq_nonneg r]
  · push Not at hcs
    have hsq_le : (c₀ - s_val) ^ 2 ≤ chi_val := by
      have h1 : (c₀ - s_val) ^ 2 ≤ ((d_U : ℝ) / (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hcs.le hc₀_sub 2
      exact le_trans h1 hchi_ge_sq
    have hsq_r : 0 ≤ ((c₀ - s_val) - r) ^ 2 := sq_nonneg _
    nlinarith

/-- **Theorem C2 (Universal Sink Unconditional Branch, `α_CSS = 1`, exact `≥ 0`!)**: -/
theorem css_ineq_of_universal_sink {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (r_sink : Fin k)
    (hsink : ∀ i : Fin k, i ≠ r_sink → G₀.adj (v i) (v r_sink)) :
    0 ≤ ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  rcases (commonOutSet G₀ v).eq_empty_or_nonempty with h_emp | h_ne
  · have hsub : G₀.toDigraph.outSet (v r_sink) ⊆ srcStarSet G₀ v := by
      intro x hx
      rw [Digraph.mem_outSet] at hx
      have hnotU : x ∉ commonOutSet G₀ v := by rw [h_emp]; simp
      simp only [commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnotU
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hnotU⟩⟩
      intro i hxi
      by_cases hir : i = r_sink
      · rw [hir] at hxi; exact G₀.asymm (v r_sink) x hx hxi
      · exact hG₀ ⟨v i, v r_sink, x, hsink i hir, hx, hxi⟩
    have hcard_ge : (G₀.toDigraph.outDeg (v r_sink) : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hs_ge : c₀ ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]; linarith [hreg (v r_sink), hcard_ge]
    have hchi_nn : 0 ≤ ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2) :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    nlinarith [sq_nonneg r]
  · exact css_ineq_of_commonOut_nonempty hn G₀ hG₀ hr hreg v h_ne

/-- **Theorem C2 Upgraded (`α_CSS = 5/6`, Conditional / Nonempty `U(v)` Branch)**:
Whenever `(commonOutSet G₀ v).Nonempty`, for ANY `r ≥ 0`,
`(5/6) * (chiPairSet.card / n²) + 2 * r * (srcStarSet.card / n) + (r² - 2 * c₀ * r) ≥ 0`! -/
theorem css56_ineq_of_commonOut_nonempty {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (hU : (commonOutSet G₀ v).Nonempty) :
    0 ≤ (5 / 6 : ℝ) * (((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  let U := commonOutSet G₀ v
  have _ : Nonempty {z : Fin n // z ∈ U} := Finset.Nonempty.to_subtype hU
  obtain ⟨w, hw_sq⟩ :=
    (G₀.induce U).exists_six_outDeg_sq_le_five_ordNonEdges (G₀.triangleFree_induce hG₀ U)
  let embU : ({z : Fin n // z ∈ U} × {z : Fin n // z ∈ U}) ↪ Fin n × Fin n :=
    ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
      rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
      injection h with ha hb; subst ha; subst hb; rfl⟩
  have hord_le_chi : (G₀.induce U).ordNonEdges ≤ (chiPairSet G₀ v).card := by
    let raw := Finset.univ.filter fun p : {z : Fin n // z ∈ U} × {z : Fin n // z ∈ U} =>
      p.1 ≠ p.2 ∧ ¬ (G₀.induce U).adj p.1 p.2 ∧ ¬ (G₀.induce U).adj p.2 p.1
    have hsub : raw.map embU ⊆ chiPairSet G₀ v := by
      intro p hp
      rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy, rfl⟩
      have hxU := (Finset.mem_filter.mp hx).2
      have hyU := (Finset.mem_filter.mp hy).2
      have hne := (Finset.mem_filter.mp hxy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hxU, hyU, hne.2.1, hne.2.2⟩⟩
    calc (G₀.induce U).ordNonEdges = (raw.map embU).card := (Finset.card_map embU).symm
      _ ≤ (chiPairSet G₀ v).card := Finset.card_le_card hsub
  have hw_all : ∀ i : Fin k, G₀.adj (v i) w.1 := (Finset.mem_filter.mp w.2).2
  have hsub_src : G₀.toDigraph.outSet w.1 \ U ⊆ srcStarSet G₀ v := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_out, hx_notU⟩
    rw [Digraph.mem_outSet] at hx_out
    simp only [U, commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx_notU
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hx_notU⟩⟩
    intro i hxi
    exact hG₀ ⟨v i, w.1, x, hw_all i, hx_out, hxi⟩
  let d_U : ℕ := (G₀.induce U).toDigraph.outDeg w
  have hd_U_eq : d_U = (U ∩ G₀.toDigraph.outSet w.1).card := G₀.outDeg_induce U w
  have hsdiff_card : (G₀.toDigraph.outSet w.1).card ≤ (srcStarSet G₀ v).card + d_U := by
    have h1 := Finset.card_le_card hsub_src
    have h2 := Finset.card_sdiff_add_card_inter (G₀.toDigraph.outSet w.1) U
    rw [Finset.inter_comm, ← hd_U_eq] at h2
    omega
  have hd_sq_chi : 6 * (d_U : ℝ) ^ 2 ≤ 5 * ((chiPairSet G₀ v).card : ℝ) := by
    have hnat : 6 * (d_U * d_U) ≤ 5 * (chiPairSet G₀ v).card := by
      have h1 : 6 * (d_U * d_U) ≤ 6 * (d_U * (d_U + 1)) :=
        Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left d_U (Nat.le_succ d_U))
      exact le_trans h1 (le_trans hw_sq (Nat.mul_le_mul_left 5 hord_le_chi))
    have hcast : ((6 * (d_U * d_U) : ℕ) : ℝ) ≤ ((5 * (chiPairSet G₀ v).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    simpa [sq] using hcast
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  let s_val : ℝ := ((srcStarSet G₀ v).card : ℝ) / (n : ℝ)
  let chi_val : ℝ := ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)
  have hc₀_sub : c₀ - s_val ≤ (d_U : ℝ) / (n : ℝ) := by
    dsimp [s_val]
    have hreal : c₀ * (n : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (d_U : ℝ) := by
      have hcast : (G₀.toDigraph.outDeg w.1 : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (d_U : ℝ) := by
        exact_mod_cast hsdiff_card
      linarith [hreg w.1, hcast]
    calc c₀ - ((srcStarSet G₀ v).card : ℝ) / (n : ℝ)
        = (c₀ * (n : ℝ) - ((srcStarSet G₀ v).card : ℝ)) / (n : ℝ) := by field_simp [hn_pos.ne']
      _ ≤ (d_U : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right (by linarith) hn_pos.le
  have hchi_ge_sq : ((d_U : ℝ) / (n : ℝ)) ^ 2 ≤ (5 / 6 : ℝ) * chi_val := by
    dsimp [chi_val]
    rw [div_pow]
    have hdiv := div_le_div_of_nonneg_right hd_sq_chi (sq_nonneg (n : ℝ))
    rw [mul_div_assoc, mul_div_assoc] at hdiv
    linarith
  have hchi_nn : 0 ≤ chi_val := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  by_cases hcs : c₀ - s_val ≤ 0
  · nlinarith [sq_nonneg r]
  · push Not at hcs
    have hsq_le : (c₀ - s_val) ^ 2 ≤ (5 / 6 : ℝ) * chi_val :=
      le_trans (pow_le_pow_left₀ hcs.le hc₀_sub 2) hchi_ge_sq
    have hsq_r : 0 ≤ ((c₀ - s_val) - r) ^ 2 := sq_nonneg _
    nlinarith

/-- **Theorem C2 Upgraded (`α_CSS = 5/6`, Universal Sink Unconditional Branch)**: -/
theorem css56_ineq_of_universal_sink {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (r_sink : Fin k)
    (hsink : ∀ i : Fin k, i ≠ r_sink → G₀.adj (v i) (v r_sink)) :
    0 ≤ (5 / 6 : ℝ) * (((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  rcases (commonOutSet G₀ v).eq_empty_or_nonempty with h_emp | h_ne
  · have hsub : G₀.toDigraph.outSet (v r_sink) ⊆ srcStarSet G₀ v := by
      intro x hx
      rw [Digraph.mem_outSet] at hx
      have hnotU : x ∉ commonOutSet G₀ v := by rw [h_emp]; simp
      simp only [commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnotU
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hnotU⟩⟩
      intro i hxi
      by_cases hir : i = r_sink
      · rw [hir] at hxi; exact G₀.asymm (v r_sink) x hx hxi
      · exact hG₀ ⟨v i, v r_sink, x, hsink i hir, hx, hxi⟩
    have hcard_ge : (G₀.toDigraph.outDeg (v r_sink) : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hs_ge : c₀ ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]; linarith [hreg (v r_sink), hcard_ge]
    have hchi_nn : 0 ≤ ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2) :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    nlinarith [sq_nonneg r]
  · exact css56_ineq_of_commonOut_nonempty hn G₀ hG₀ hr hreg v h_ne

/-- **Theorem C2 (`α_CSS = 1037/1250`, Conditional / Nonempty `U(v)` Branch)**:
Whenever `(commonOutSet G₀ v).Nonempty`, for ANY `r ≥ 0`,
`(1037/1250) * (chiPairSet.card / n²) + 2 * r * (srcStarSet.card / n) + (r² - 2 * c₀ * r) ≥ 0`! -/
theorem cssSharp_ineq_of_commonOut_nonempty {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (hU : (commonOutSet G₀ v).Nonempty) :
    0 ≤ (1037 / 1250 : ℝ) * (((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  let U := commonOutSet G₀ v
  have _ : Nonempty {z : Fin n // z ∈ U} := Finset.Nonempty.to_subtype hU
  obtain ⟨w, hw_sq⟩ :=
    (G₀.induce U).exists_outDeg_sq_le_1037_ordNonEdges (G₀.triangleFree_induce hG₀ U)
  let embU : ({z : Fin n // z ∈ U} × {z : Fin n // z ∈ U}) ↪ Fin n × Fin n :=
    ⟨fun p => (p.1.1, p.2.1), fun p₁ p₂ h => by
      rcases p₁ with ⟨⟨a₁, _⟩, ⟨b₁, _⟩⟩; rcases p₂ with ⟨⟨a₂, _⟩, ⟨b₂, _⟩⟩
      injection h with ha hb; subst ha; subst hb; rfl⟩
  have hord_le_chi : (G₀.induce U).ordNonEdges ≤ (chiPairSet G₀ v).card := by
    let raw := Finset.univ.filter fun p : {z : Fin n // z ∈ U} × {z : Fin n // z ∈ U} =>
      p.1 ≠ p.2 ∧ ¬ (G₀.induce U).adj p.1 p.2 ∧ ¬ (G₀.induce U).adj p.2 p.1
    have hsub : raw.map embU ⊆ chiPairSet G₀ v := by
      intro p hp
      rcases Finset.mem_map.mp hp with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy, rfl⟩
      have hxU := (Finset.mem_filter.mp hx).2
      have hyU := (Finset.mem_filter.mp hy).2
      have hne := (Finset.mem_filter.mp hxy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hxU, hyU, hne.2.1, hne.2.2⟩⟩
    calc (G₀.induce U).ordNonEdges = (raw.map embU).card := (Finset.card_map embU).symm
      _ ≤ (chiPairSet G₀ v).card := Finset.card_le_card hsub
  have hw_all : ∀ i : Fin k, G₀.adj (v i) w.1 := (Finset.mem_filter.mp w.2).2
  have hsub_src : G₀.toDigraph.outSet w.1 \ U ⊆ srcStarSet G₀ v := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_out, hx_notU⟩
    rw [Digraph.mem_outSet] at hx_out
    simp only [U, commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx_notU
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hx_notU⟩⟩
    intro i hxi
    exact hG₀ ⟨v i, w.1, x, hw_all i, hx_out, hxi⟩
  let d_U : ℕ := (G₀.induce U).toDigraph.outDeg w
  have hd_U_eq : d_U = (U ∩ G₀.toDigraph.outSet w.1).card := G₀.outDeg_induce U w
  have hsdiff_card : (G₀.toDigraph.outSet w.1).card ≤ (srcStarSet G₀ v).card + d_U := by
    have h1 := Finset.card_le_card hsub_src
    have h2 := Finset.card_sdiff_add_card_inter (G₀.toDigraph.outSet w.1) U
    rw [Finset.inter_comm, ← hd_U_eq] at h2
    omega
  have hd_sq_chi : 1250 * (d_U : ℝ) ^ 2 ≤ 1037 * ((chiPairSet G₀ v).card : ℝ) := by
    have hnat : 1250 * (d_U * d_U) ≤ 1037 * (chiPairSet G₀ v).card := by
      have h1 : 1250 * (d_U * d_U) ≤ 1250 * (d_U * (d_U + 1)) :=
        Nat.mul_le_mul_left 1250 (Nat.mul_le_mul_left d_U (Nat.le_succ d_U))
      exact le_trans h1 (le_trans hw_sq (Nat.mul_le_mul_left 1037 hord_le_chi))
    have hcast : ((1250 * (d_U * d_U) : ℕ) : ℝ) ≤ ((1037 * (chiPairSet G₀ v).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    simpa [sq] using hcast
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  let s_val : ℝ := ((srcStarSet G₀ v).card : ℝ) / (n : ℝ)
  let chi_val : ℝ := ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)
  have hc₀_sub : c₀ - s_val ≤ (d_U : ℝ) / (n : ℝ) := by
    dsimp [s_val]
    have hreal : c₀ * (n : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (d_U : ℝ) := by
      have hcast : (G₀.toDigraph.outDeg w.1 : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) + (d_U : ℝ) := by
        exact_mod_cast hsdiff_card
      linarith [hreg w.1, hcast]
    calc c₀ - ((srcStarSet G₀ v).card : ℝ) / (n : ℝ)
        = (c₀ * (n : ℝ) - ((srcStarSet G₀ v).card : ℝ)) / (n : ℝ) := by field_simp [hn_pos.ne']
      _ ≤ (d_U : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right (by linarith) hn_pos.le
  have hchi_ge_sq : ((d_U : ℝ) / (n : ℝ)) ^ 2 ≤ (1037 / 1250 : ℝ) * chi_val := by
    dsimp [chi_val]
    rw [div_pow]
    have hdiv := div_le_div_of_nonneg_right hd_sq_chi (sq_nonneg (n : ℝ))
    rw [mul_div_assoc, mul_div_assoc] at hdiv
    linarith
  have hchi_nn : 0 ≤ chi_val := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  by_cases hcs : c₀ - s_val ≤ 0
  · nlinarith [sq_nonneg r]
  · push Not at hcs
    have hsq_le : (c₀ - s_val) ^ 2 ≤ (1037 / 1250 : ℝ) * chi_val :=
      le_trans (pow_le_pow_left₀ hcs.le hc₀_sub 2) hchi_ge_sq
    have hsq_r : 0 ≤ ((c₀ - s_val) - r) ^ 2 := sq_nonneg _
    nlinarith

/-- **Theorem C2 (`α_CSS = 1037/1250`, Universal Sink Unconditional Branch)**: -/
theorem cssSharp_ineq_of_universal_sink {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (r_sink : Fin k)
    (hsink : ∀ i : Fin k, i ≠ r_sink → G₀.adj (v i) (v r_sink)) :
    0 ≤ (1037 / 1250 : ℝ) * (((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  rcases (commonOutSet G₀ v).eq_empty_or_nonempty with h_emp | h_ne
  · have hsub : G₀.toDigraph.outSet (v r_sink) ⊆ srcStarSet G₀ v := by
      intro x hx
      rw [Digraph.mem_outSet] at hx
      have hnotU : x ∉ commonOutSet G₀ v := by rw [h_emp]; simp
      simp only [commonOutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnotU
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨?_, hnotU⟩⟩
      intro i hxi
      by_cases hir : i = r_sink
      · rw [hir] at hxi; exact G₀.asymm (v r_sink) x hx hxi
      · exact hG₀ ⟨v i, v r_sink, x, hsink i hir, hx, hxi⟩
    have hcard_ge : (G₀.toDigraph.outDeg (v r_sink) : ℝ) ≤ ((srcStarSet G₀ v).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hs_ge : c₀ ≤ ((srcStarSet G₀ v).card : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]; linarith [hreg (v r_sink), hcard_ge]
    have hchi_nn : 0 ≤ ((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2) :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    nlinarith [sq_nonneg r]
  · exact cssSharp_ineq_of_commonOut_nonempty hn G₀ hG₀ hr hreg v h_ne

theorem css83_ineq_of_commonOut_nonempty {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (hU : (commonOutSet G₀ v).Nonempty) :
    0 ≤ (83 / 100 : ℝ) * (((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  have hs := cssSharp_ineq_of_commonOut_nonempty hn G₀ hG₀ hr hreg v hU
  have hχ := div_nonneg (Nat.cast_nonneg ((chiPairSet G₀ v).card) : (0 : ℝ) ≤ _) (sq_nonneg (n : ℝ))
  linarith

theorem css83_ineq_of_universal_sink {n k : ℕ} (hn : 0 < n)
    (G₀ : OrientedGraph (Fin n)) [DecidableRel G₀.adj] (hG₀ : G₀.TriangleFree)
    {c₀ r : ℝ} (hr : 0 ≤ r)
    (hreg : ∀ w : Fin n, (G₀.toDigraph.outDeg w : ℝ) = c₀ * (n : ℝ))
    (v : Fin k → Fin n) (r_sink : Fin k)
    (hsink : ∀ i : Fin k, i ≠ r_sink → G₀.adj (v i) (v r_sink)) :
    0 ≤ (83 / 100 : ℝ) * (((chiPairSet G₀ v).card : ℝ) / ((n : ℝ) ^ 2)) +
      2 * r * (((srcStarSet G₀ v).card : ℝ) / (n : ℝ)) + (r ^ 2 - 2 * c₀ * r) := by
  have hs := cssSharp_ineq_of_universal_sink hn G₀ hG₀ hr hreg v r_sink hsink
  have hχ := div_nonneg (Nat.cast_nonneg ((chiPairSet G₀ v).card) : (0 : ℝ) ≤ _) (sq_nonneg (n : ℝ))
  linarith

/-! ## Section 4: Section 5 Two-Endpoint Affine Interval Closure (`[c_low, c_high]`) -/

/-- **Master Two-Endpoint Affine Interval Certificate Theorem**:
Suppose `cStar ≤ c_high` is already established, and an affine-in-`c` flag functional
`S(c, H) = U_fn H + c * V_fn H` on `OrientedGraph (Fin m)` satisfies:
1. On any `ε`-extremal `G₀` from Theorem B1 (`cStar - ε < c₀ ≤ cStar`), its `tupleWeight`
   expectation is at least `-M_ind * ε` (`0 ≤ M_ind`);
2. At BOTH endpoints `c_low` and `c_high` (`c_low ≤ c_high`), every `C₃`-free `H` on `Fin m`
   satisfies `symPerm (S c_low) H < 0` and `symPerm (S c_high) H < 0`.
Then `cStar < c_low`, and EVERY finite nonempty simple digraph with minimum out-degree
`≥ c_low * |V|` contains a directed cycle of length `≤ 3`! -/
theorem hasCycleLe3_of_interval_certificate {m : ℕ} {c_low c_high M_ind : ℝ}
    (hc_le : c_low ≤ c_high) (hcStar_high : cStar ≤ c_high) (hM_nn : 0 ≤ M_ind)
    (U_fn V_fn : OrientedGraph (Fin m) → ℝ)
    (h_expect_ge : ∀ {n : ℕ} (_hn : 0 < n) {c₀ ε : ℝ} (_hε : 0 < ε)
      (G₀ : OrientedGraph (Fin n)) (dG₀ : DecidableRel G₀.adj),
      G₀.TriangleFree →
      (∀ u : Fin n, @Digraph.outWeight (Fin n) _ G₀.toDigraph dG₀ (unifWeight (Fin n)) u = c₀) →
      (∀ U : Finset (Fin n), U.Nonempty →
        ∃ w ∈ U, ((U ∩ @Digraph.outSet (Fin n) _ G₀.toDigraph dG₀ w).card : ℝ) ≤
          (c₀ + ε) * (U.card : ℝ)) →
      -M_ind * ε ≤ ∑ x : Fin m → Fin n,
        tupleWeight (unifWeight (Fin n)) x *
          (U_fn (G₀.pullback x) + c₀ * V_fn (G₀.pullback x)))
    -- Finite uniform slack & slope bound across C₃-free graphs on Fin m:
    {δ V_max : ℝ} (hδ_pos : 0 < δ) (hV_nn : 0 ≤ V_max)
    (h_slack_low : ∀ H : OrientedGraph (Fin m), H.TriangleFree →
      symPerm (fun K => U_fn K + c_low * V_fn K) H ≤ -δ)
    (h_slack_high : ∀ H : OrientedGraph (Fin m), H.TriangleFree →
      symPerm (fun K => U_fn K + c_high * V_fn K) H ≤ -δ)
    (h_slope_bdd : ∀ H : OrientedGraph (Fin m), H.TriangleFree →
      |symPerm V_fn H| ≤ V_max) :
    ∀ {V : Type u} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj],
      (∀ u : V, c_low * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) →
      G.HasCycleLe3 := by
  have hcStar_lt : cStar < c_low := by
    by_contra hge
    push Not at hge
    let P_card : ℝ := (Fintype.card (Equiv.Perm (Fin m)) : ℝ)
    have hperm_nn : (0 : ℝ) ≤ P_card := Nat.cast_nonneg _
    let denom : ℝ := 2 * (P_card * M_ind + V_max + 1)
    have hPM_nn : 0 ≤ P_card * M_ind := mul_nonneg hperm_nn hM_nn
    have hdenom_pos : 0 < denom := by dsimp [denom]; linarith
    let ε : ℝ := δ / denom
    have hε_pos : 0 < ε := div_pos hδ_pos hdenom_pos
    obtain ⟨n, hn, c₀, G₀, dG₀, hc₀_gt, hc₀_le, hG₀_tri, hG₀_reg, hG₀_hered⟩ :=
      exists_eps_extremal_regular_orientedGraph hε_pos
    have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hexp := h_expect_ge hn hε_pos G₀ dG₀ hG₀_tri hG₀_reg hG₀_hered
    let S_c₀ : OrientedGraph (Fin m) → ℝ := fun K => U_fn K + c₀ * V_fn K
    have hsym_exp : -P_card * M_ind * ε ≤ ∑ x : Fin m → Fin n,
        tupleWeight (unifWeight (Fin n)) x * symPerm S_c₀ (G₀.pullback x) := by
      unfold symPerm
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hconst : ∑ π : Equiv.Perm (Fin m),
          (∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x *
            S_c₀ ((G₀.pullback x).relabel π)) =
        P_card * (∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x * S_c₀ (G₀.pullback x)) := by
        have h_each : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))),
            (∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x *
              S_c₀ ((G₀.pullback x).relabel π)) =
            (∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x * S_c₀ (G₀.pullback x)) :=
          fun π _ => sum_tupleWeight_relabel G₀ (unifWeight (Fin n)) S_c₀ π
        rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hconst]
      nlinarith
    -- Pointwise upper bound on symPerm S_c₀ H for any C₃-free H on Fin m
    have h_pt_ub : ∀ H : OrientedGraph (Fin m), H.TriangleFree →
        symPerm S_c₀ H ≤ -δ + V_max * ε := by
      intro H hH
      have hsym_lin : ∀ c : ℝ, symPerm (fun K => U_fn K + c * V_fn K) H =
          symPerm U_fn H + c * symPerm V_fn H := by
        intro c
        unfold symPerm
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have h_lo := h_slack_low H hH
      have h_hi := h_slack_high H hH
      rw [hsym_lin] at h_lo h_hi
      have h_c0_eq : symPerm S_c₀ H = symPerm U_fn H + c₀ * symPerm V_fn H := hsym_lin c₀
      rw [h_c0_eq]
      by_cases h_in : c_low ≤ c₀
      · have hc₀_hi : c₀ ≤ c_high := le_trans hc₀_le hcStar_high
        by_cases h_eq : c_low = c_high
        · have hc_eq : c₀ = c_low := by linarith
          rw [hc_eq]
          nlinarith
        · have h_diff : 0 < c_high - c_low := by
            rcases lt_or_eq_of_le hc_le with hlt | heq
            · linarith
            · exact (h_eq heq).elim
          have ht0 : 0 ≤ (c_high - c₀) / (c_high - c_low) :=
            div_nonneg (by linarith) h_diff.le
          have ht1 : 0 ≤ (c₀ - c_low) / (c_high - c_low) :=
            div_nonneg (by linarith) h_diff.le
          have hconv : symPerm U_fn H + c₀ * symPerm V_fn H =
              ((c_high - c₀) / (c_high - c_low)) * (symPerm U_fn H + c_low * symPerm V_fn H) +
                ((c₀ - c_low) / (c_high - c_low)) * (symPerm U_fn H + c_high * symPerm V_fn H) := by
            field_simp [h_diff.ne']
            ring
          have hsum1 : (c_high - c₀) / (c_high - c_low) + (c₀ - c_low) / (c_high - c_low) = 1 := by
            field_simp [h_diff.ne']
            ring
          rw [hconv]
          nlinarith
      · push Not at h_in
        have h_gap : c_low - c₀ < ε := by linarith
        have hv_abs := abs_le.mp (h_slope_bdd H hH)
        have h_shift : (c₀ - c_low) * symPerm V_fn H ≤ V_max * ε := by
          have : -(c_low - c₀) * symPerm V_fn H ≤ (c_low - c₀) * V_max := by
            nlinarith [hv_abs.1, hv_abs.2]
          nlinarith
        linarith
    -- Integrate pointwise bound over tupleWeight (unifWeight (Fin n))
    let hw : IsProbWeight (unifWeight (Fin n)) := isProbWeight_unifWeight
    have h_exp_ub : ∑ x : Fin m → Fin n,
        tupleWeight (unifWeight (Fin n)) x * symPerm S_c₀ (G₀.pullback x) ≤ -δ + V_max * ε := by
      have hterm : ∀ x ∈ (Finset.univ : Finset (Fin m → Fin n)),
          tupleWeight (unifWeight (Fin n)) x * symPerm S_c₀ (G₀.pullback x) ≤
            tupleWeight (unifWeight (Fin n)) x * (-δ + V_max * ε) := by
        intro x _
        exact mul_le_mul_of_nonneg_left
          (h_pt_ub (G₀.pullback x) (G₀.triangleFree_pullback hG₀_tri x))
          (tupleWeight_nonneg hw x)
      calc ∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x * symPerm S_c₀ (G₀.pullback x)
          ≤ ∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x * (-δ + V_max * ε) :=
            Finset.sum_le_sum hterm
        _ = (∑ x : Fin m → Fin n, tupleWeight (unifWeight (Fin n)) x) * (-δ + V_max * ε) := by
            rw [← Finset.sum_mul]
        _ = -δ + V_max * ε := by rw [sum_tupleWeight hw, one_mul]
    have hε_eq : ε * denom = δ := div_mul_cancel₀ δ hdenom_pos.ne'
    have h_comb : -P_card * M_ind * ε ≤ -δ + V_max * ε := le_trans hsym_exp h_exp_ub
    dsimp [denom] at hε_eq
    nlinarith
  intro V _ _ G _ hdeg
  refine hasCycleLe3_of_oriented_bound (c := c_low) ?_ G hdeg
  intro H0 d0 hH0
  by_contra hno
  push Not at hno
  have hle := @le_cStar_of_orientedGraph V _ _ H0 d0 hH0 c_low hno
  linarith

/-- **Chaining Lemma (`HasCycleLe3` at `c` → `cStar ≤ c`)**:
Any Caccetta–Häggkvist bound `c` valid on finite simple digraphs immediately implies `cStar ≤ c`,
allowing seamless chaining of `hasCycleLe3_of_flag_certificate` and `hasCycleLe3_of_interval_certificate`! -/
theorem cStar_le_of_hasCycleLe3 {c : ℝ}
    (h_ch : ∀ {V : Type} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj],
      (∀ u : V, c * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) → G.HasCycleLe3) :
    cStar ≤ c := by
  refine csSup_le c3FreeRatios_nonempty fun r hr => ?_
  rcases hr with ⟨n, hn, H, dH, htri, hdeg⟩
  by_contra hgt
  push Not at hgt
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdeg_c : ∀ u : Fin n,
      c * (Fintype.card (Fin n) : ℝ) ≤ (@Digraph.outDeg (Fin n) _ H.toDigraph dH u : ℝ) := by
    intro u
    rw [Fintype.card_fin]
    have hlt : c * (n : ℝ) < r * (n : ℝ) := mul_lt_mul_of_pos_right hgt hn_pos
    exact le_trans hlt.le (hdeg u)
  rcases @h_ch (Fin n) _ _ H.toDigraph dH hdeg_c with ⟨u, v, huv, hvu⟩ | htri'
  · exact H.asymm u v huv hvu
  · exact htri htri'

end CaccettaHaggkvist
