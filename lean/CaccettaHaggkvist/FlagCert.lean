module

public import CaccettaHaggkvist.Basic
public import CaccettaHaggkvist.Analytical
public import CaccettaHaggkvist.WeightBridge

/-!
# Exact Q-SOS Flag Algebra Certificate Soundness & Kernel Verifier Framework

This module proves the complete, limit-free, probability-free soundness bridge for exact integer
Q-SOS Flag Algebra certificates (`mode = "ge"` AND `mode = "eq"`!) on ALL finite simple digraphs:

1. **Deterministic Exact-Degree Blow-Up Regularization (`exists_regular_subOrientedGraph_blowup`)**:
   If a finite nonempty `C₃`-free `OrientedGraph V` satisfies `∀ u, (c_num / c_den) * |V| ≤ outDeg u`
   (`0 < c_den`), then its `c_den`-fold blow-up contains a deterministic `C₃`-free spanning
   oriented subgraph `H_reg` on `W = V × Fin c_den` in which EVERY vertex `p : W` has exact
   uniform out-weight `(c_den : ℝ) * outWeight (unifWeight W) p = (c_num : ℝ)`.
2. **Exact Zero-Expectation 1-Rooted Linear Regularity Terms (`expect_degLinearTerm_eq_zero`)**:
   For ANY function `g : OrientedGraph (Fin (r + 1)) → ℝ` on coordinates `{0, 2, ..., r + 1}`,
   `g(H|_{0,2..}) * (c_den * 1[H.adj 0 1] - c_num)` has **exact expectation `0`** under
   `tupleWeight (unifWeight W)` on `H_reg` (allowing arbitrary signed multipliers `λ_F ∈ ℤ`!).
3. **Exact Non-Negative Factored SOS Terms (`expect_sosFactorTerm_nonneg`)**:
   For ANY split `k + d + d = m`, non-negative type indicator `σ_ind ≥ 0`, positive weight `wt ≥ 0`,
   and vector function `u_fn : OrientedGraph (Fin (k + d)) → ℝ`,
   `wt * σ_ind(H|_{0..k-1}) * u_fn(H|_{0..k+d-1}) * u_fn(H|_{0..k-1, k+d..m-1})` has **exact
   expectation `≥ 0`** under `tupleWeight w`!
4. **`Perm (Fin m)`-Symmetrized Contradiction Theorem (`hasCycleLe3_of_flag_certificate`)**:
   If `F` has expectation `≥ 0` on `H_reg` and its `S_m`-symmetrization
   `symPerm F H = ∑ π : Perm (Fin m), F (H.relabel π)` is strictly negative (`< 0`) on EVERY
   `C₃`-free `OrientedGraph (Fin m)`, then EVERY finite nonempty simple digraph with
   `δ⁺(G) ≥ (c_num / c_den) * |V|` has `G.HasCycleLe3`!
-/

@[expose] public section

namespace CaccettaHaggkvist

open scoped BigOperators

universe u

/-! ## Section 1: Deterministic Exact-Degree Regularization on `G.blowup c_den` -/

/-- **Deterministic Exact-Degree Blow-Up Regularization**:
From `∀ u : V, ((c_num : ℝ) / (c_den : ℝ)) * |V| ≤ outDeg u` (`0 < c_den`), constructs a
deterministic `C₃`-free oriented graph `H_reg` on `V × Fin c_den` where EVERY vertex has exact
out-degree `c_num * |V|`, hence exact uniform out-weight `c_num / c_den`. -/
theorem OrientedGraph.exists_regular_subOrientedGraph_blowup
    {V : Type u} [Fintype V] [Nonempty V]
    (G : OrientedGraph V) [DecidableRel G.adj] (hG : G.TriangleFree)
    {c_num c_den : ℕ} (hc_den : 0 < c_den)
    (hdeg : ∀ u : V, ((c_num : ℝ) / (c_den : ℝ)) * (Fintype.card V : ℝ) ≤
      (G.toDigraph.outDeg u : ℝ)) :
    have _ : Nonempty (Fin c_den) := ⟨⟨0, hc_den⟩⟩
    ∃ (H_reg : OrientedGraph (V × Fin c_den)) (dH : DecidableRel H_reg.adj),
      H_reg.TriangleFree ∧
      ∀ p : V × Fin c_den,
        (c_den : ℝ) * @Digraph.outWeight (V × Fin c_den) _ H_reg.toDigraph dH
          (unifWeight (V × Fin c_den)) p = (c_num : ℝ) := by
  have _ : Nonempty (Fin c_den) := ⟨⟨0, hc_den⟩⟩
  let B : OrientedGraph (V × Fin c_den) := G.blowup c_den
  have hB_tri : B.TriangleFree := G.triangleFree_blowup hG c_den
  have hcard_ge : ∀ p : V × Fin c_den,
      c_num * Fintype.card V ≤ (B.toDigraph.outSet p).card := by
    intro p
    have hdeg_p := hdeg p.1
    have hcd_pos : (0 : ℝ) < (c_den : ℝ) := Nat.cast_pos.mpr hc_den
    have hreal : (c_num : ℝ) * (Fintype.card V : ℝ) ≤
        (G.toDigraph.outDeg p.1 : ℝ) * (c_den : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hdeg_p hcd_pos.le
      calc (c_num : ℝ) * (Fintype.card V : ℝ)
          = ((c_num : ℝ) / (c_den : ℝ)) * (Fintype.card V : ℝ) * (c_den : ℝ) := by
            field_simp [hcd_pos.ne']
        _ ≤ (G.toDigraph.outDeg p.1 : ℝ) * (c_den : ℝ) := hmul
    have hnat : c_num * Fintype.card V ≤ G.toDigraph.outDeg p.1 * c_den := by
      exact_mod_cast hreal
    have hout : (B.toDigraph.outSet p).card = G.toDigraph.outDeg p.1 * c_den :=
      G.outDeg_blowup c_den p
    omega
  choose S hS_sub hS_card using fun p =>
    Finset.exists_subset_card_eq (hcard_ge p)
  let _ : DecidableEq (V × Fin c_den) := Classical.decEq (V × Fin c_den)
  let H_reg : OrientedGraph (V × Fin c_den) :=
    { adj := fun p q => q ∈ S p
      loopless := fun p hp => B.loopless p ((Digraph.mem_outSet B.toDigraph).mp (hS_sub p hp))
      asymm := fun p q hpq hqp =>
        B.asymm p q ((Digraph.mem_outSet B.toDigraph).mp (hS_sub p hpq))
          ((Digraph.mem_outSet B.toDigraph).mp (hS_sub q hqp)) }
  let dH : DecidableRel H_reg.adj := fun p q => Finset.decidableMem q (S p)
  refine ⟨H_reg, dH, ?_, ?_⟩
  · rintro ⟨p, q, r, hpq, hqr, hrp⟩
    exact hB_tri ⟨p, q, r,
      (Digraph.mem_outSet B.toDigraph).mp (hS_sub p hpq),
      (Digraph.mem_outSet B.toDigraph).mp (hS_sub q hqr),
      (Digraph.mem_outSet B.toDigraph).mp (hS_sub r hrp)⟩
  · intro p
    have hout_eq : @Digraph.outSet (V × Fin c_den) _ H_reg.toDigraph dH p = S p := by
      ext q
      simp [Digraph.outSet, H_reg]
    have hdeg_eq : @Digraph.outDeg (V × Fin c_den) _ H_reg.toDigraph dH p =
        c_num * Fintype.card V := by
      dsimp [Digraph.outDeg]
      rw [hout_eq, hS_card p]
    rw [@Digraph.outWeight_unifWeight (V × Fin c_den) _ H_reg.toDigraph dH p,
      hdeg_eq, Fintype.card_prod, Fintype.card_fin]
    have hV_pos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hcd_pos : (0 : ℝ) < (c_den : ℝ) := Nat.cast_pos.mpr hc_den
    push_cast
    field_simp [hV_pos.ne', hcd_pos.ne']

/-! ## Section 2: Zero-Expectation 1-Rooted Linear Regularity Terms -/

/-- Coordinate embedding `Fin (r + 1) → Fin (r + 2)` skipping coordinate `1` (`0 ↦ 0`,
`i + 1 ↦ i + 2`), isolating the test arc `0 → 1` from the `(r + 1)`-vertex 1-flag. -/
def embSkipOne {r : ℕ} (i : Fin (r + 1)) : Fin (r + 2) :=
  Fin.cases 0 (fun j => j.succ.succ) i

/-- Single 1-rooted degree-regularity linear term on `OrientedGraph (Fin (r + 2))`. -/
noncomputable def degLinearTerm {r : ℕ} (g : OrientedGraph (Fin (r + 1)) → ℝ)
    (c_num c_den : ℕ) (H : OrientedGraph (Fin (r + 2))) : ℝ :=
  g (H.pullback embSkipOne) *
    ((@ite ℝ (H.adj 0 1) (Classical.propDecidable _) (c_den : ℝ) 0) - (c_num : ℝ))

/-- **Exact Zero-Expectation Lemma for 1-Rooted Linear Terms**:
On any probability-weighted digraph `(H_reg, w)` satisfying `(c_den : ℝ) * outWeight w u = c_num`
for all `u`, `degLinearTerm g c_num c_den` has expectation identically `0` for EVERY `g`! -/
theorem expect_degLinearTerm_eq_zero {W : Type u} [Fintype W] {r : ℕ}
    (H_reg : OrientedGraph W) [DecidableRel H_reg.adj]
    {w : W → ℝ} (hw : IsProbWeight w)
    {c_num c_den : ℕ}
    (hreg : ∀ u : W, (c_den : ℝ) * H_reg.toDigraph.outWeight w u = (c_num : ℝ))
    (g : OrientedGraph (Fin (r + 1)) → ℝ) :
    ∑ x : Fin (r + 2) → W,
      tupleWeight w x * degLinearTerm g c_num c_den (H_reg.pullback x) = 0 := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 2) => W)), Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => W)), Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hterm : ∀ v : W,
      tupleWeight w ((Fin.consEquiv (fun _ : Fin (r + 2) => W))
        (u, (Fin.consEquiv (fun _ : Fin (r + 1) => W)) (v, y))) *
        degLinearTerm g c_num c_den (H_reg.pullback
          ((Fin.consEquiv (fun _ : Fin (r + 2) => W))
            (u, (Fin.consEquiv (fun _ : Fin (r + 1) => W)) (v, y)))) =
      w u * tupleWeight w y * g (H_reg.pullback (Fin.cons u y)) *
        (w v * ((if H_reg.adj u v then (c_den : ℝ) else 0) - (c_num : ℝ))) := by
    intro v
    simp only [Fin.consEquiv_apply]
    have hpull : (H_reg.pullback (Fin.cons u (Fin.cons v y))).pullback embSkipOne =
        H_reg.pullback (Fin.cons u y) := by
      rw [OrientedGraph.pullback_comp]
      congr 1
      ext a
      cases a using Fin.cases <;> rfl
    have hadj :
        (@ite ℝ ((H_reg.pullback (Fin.cons u (Fin.cons v y))).adj 0 1)
          (Classical.propDecidable _) (c_den : ℝ) 0) =
        (if H_reg.adj u v then (c_den : ℝ) else 0) := by
      change (@ite ℝ (H_reg.adj u v) (Classical.propDecidable _) (c_den : ℝ) 0) = _
      by_cases huv : H_reg.adj u v <;> simp [huv]
    have htw : tupleWeight w (Fin.cons u (Fin.cons v y)) =
        w u * (w v * tupleWeight w y) := by
      unfold tupleWeight
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp_rw [Fin.cons_succ]
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp_rw [Fin.cons_succ]
    unfold degLinearTerm
    rw [hpull, hadj, htw]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  have hv_sum : ∑ v : W, w v * ((if H_reg.adj u v then (c_den : ℝ) else 0) - (c_num : ℝ)) = 0 := by
    have hsplit : ∑ v : W, w v * ((if H_reg.adj u v then (c_den : ℝ) else 0) - (c_num : ℝ)) =
        (c_den : ℝ) * (∑ v : W, if H_reg.adj u v then w v else 0) -
          (c_num : ℝ) * (∑ v : W, w v) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    have hfilter : (∑ v : W, if H_reg.adj u v then w v else 0) =
        H_reg.toDigraph.outWeight w u := by
      unfold Digraph.outWeight Digraph.outSet
      rw [Finset.sum_filter]
    rw [hsplit, hfilter, hreg u, hw.sum_eq_one, mul_one, sub_self]
  rw [hv_sum, mul_zero]

/-! ## Section 3: Non-Negative Expectation of Factored SOS Terms -/

/-- Root embedding `0..k-1` into `Fin (k + d + d)`. -/
def embRoot {k d : ℕ} (i : Fin k) : Fin (k + d + d) :=
  ⟨i.1, by omega⟩

/-- Left `(k + d)`-flag embedding `0..k+d-1` into `Fin (k + d + d)`. -/
def embLeft {k d : ℕ} (i : Fin (k + d)) : Fin (k + d + d) :=
  ⟨i.1, by omega⟩

/-- Right `(k + d)`-flag embedding `0..k-1 ∪ k+d..k+d+d-1` into `Fin (k + d + d)`. -/
def embRight {k d : ℕ} (i : Fin (k + d)) : Fin (k + d + d) :=
  if _ : i.1 < k then ⟨i.1, by omega⟩ else ⟨i.1 + d, by omega⟩

/-- Tuple concatenation `(Fin a → W) → (Fin b → W) → (Fin (a + b) → W)`. -/
def appendTuple {W : Type u} {a b : ℕ} (x : Fin a → W) (y : Fin b → W) (i : Fin (a + b)) : W :=
  if h : i.1 < a then x ⟨i.1, h⟩ else y ⟨i.1 - a, by omega⟩

lemma appendTuple_equiv {W : Type u} {a b : ℕ} :
    ∃ e : (Fin a → W) × (Fin b → W) ≃ (Fin (a + b) → W),
      ∀ p, e p = appendTuple p.1 p.2 := by
  refine ⟨{
    toFun := fun p => appendTuple p.1 p.2
    invFun := fun z => (fun i => z ⟨i.1, by omega⟩, fun j => z ⟨a + j.1, by omega⟩)
    left_inv := fun ⟨x, y⟩ => by
      ext i
      · simp [appendTuple, i.isLt]
      · have hnot : ¬ (a + i.1 < a) := by omega
        have hsub : a + i.1 - a = i.1 := by omega
        simp [appendTuple, hnot, hsub]
    right_inv := fun z => by
      ext k
      by_cases hk : k.1 < a
      · simp [appendTuple, hk]
      · have hadd : a + (k.1 - a) = k.1 := by omega
        simp [appendTuple, hk, hadd]
  }, fun _ => rfl⟩

lemma tupleWeight_appendTuple {W : Type u} {a b : ℕ} (w : W → ℝ)
    (x : Fin a → W) (y : Fin b → W) :
    tupleWeight w (appendTuple x y) = tupleWeight w x * tupleWeight w y := by
  unfold tupleWeight
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    change w (appendTuple x y ⟨i.1, _⟩) = w (x i)
    simp [appendTuple, i.isLt]
  · refine Finset.prod_congr rfl fun j _ => ?_
    change w (appendTuple x y ⟨a + j.1, _⟩) = w (y j)
    have hnot : ¬ (a + j.1 < a) := by omega
    have hsub : a + j.1 - a = j.1 := by omega
    simp [appendTuple, hnot, hsub]

/-- Single rank-1 PSD SOS factor `wt * σ_ind(H|_{root}) * u(H|_{left}) * u(H|_{right})`. -/
def sosFactorTerm {k d : ℕ} (wt : ℝ) (σ_ind : OrientedGraph (Fin k) → ℝ)
    (u_fn : OrientedGraph (Fin (k + d)) → ℝ)
    (H : OrientedGraph (Fin (k + d + d))) : ℝ :=
  wt * σ_ind (H.pullback embRoot) * u_fn (H.pullback embLeft) * u_fn (H.pullback embRight)

/-- **Exact Non-Negativity of Rank-1 SOS Factors**:
For any `wt ≥ 0`, `σ_ind ≥ 0`, and arbitrary `u_fn`, `sosFactorTerm` has expectation `≥ 0`
under `tupleWeight w` on ANY oriented graph `H_reg`! -/
theorem expect_sosFactorTerm_nonneg {W : Type u} [Fintype W] {k d : ℕ}
    (H_reg : OrientedGraph W) {w : W → ℝ} (hw : IsProbWeight w)
    {wt : ℝ} (hwt : 0 ≤ wt)
    {σ_ind : OrientedGraph (Fin k) → ℝ} (hσ : ∀ S, 0 ≤ σ_ind S)
    (u_fn : OrientedGraph (Fin (k + d)) → ℝ) :
    0 ≤ ∑ x : Fin (k + d + d) → W,
      tupleWeight w x * sosFactorTerm wt σ_ind u_fn (H_reg.pullback x) := by
  obtain ⟨e1, he1⟩ := appendTuple_equiv (W := W) (a := k + d) (b := d)
  obtain ⟨e2, he2⟩ := appendTuple_equiv (W := W) (a := k) (b := d)
  rw [← Equiv.sum_comp e1, Fintype.sum_prod_type]
  simp_rw [he1]
  have hinner : ∀ xy : Fin (k + d) → W,
      ∑ z : Fin d → W,
        tupleWeight w (appendTuple xy z) *
          sosFactorTerm wt σ_ind u_fn (H_reg.pullback (appendTuple xy z)) =
      ∑ z : Fin d → W,
        tupleWeight w xy * tupleWeight w z *
          sosFactorTerm wt σ_ind u_fn (H_reg.pullback (appendTuple xy z)) := by
    intro xy
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [tupleWeight_appendTuple]
  simp_rw [hinner]
  rw [← Equiv.sum_comp e2, Fintype.sum_prod_type]
  simp_rw [he2]
  refine Finset.sum_nonneg fun xR _ => ?_
  have hfactor : ∀ y z : Fin d → W,
      tupleWeight w (appendTuple xR y) * tupleWeight w z *
        sosFactorTerm wt σ_ind u_fn (H_reg.pullback (appendTuple (appendTuple xR y) z)) =
      (tupleWeight w xR * wt * σ_ind (H_reg.pullback xR)) *
        ((tupleWeight w y * u_fn (H_reg.pullback (appendTuple xR y))) *
          (tupleWeight w z * u_fn (H_reg.pullback (appendTuple xR z)))) := by
    intro y z
    rw [tupleWeight_appendTuple]
    have hR : (H_reg.pullback (appendTuple (appendTuple xR y) z)).pullback embRoot =
        H_reg.pullback xR := by
      have hfun : appendTuple (appendTuple xR y) z ∘ embRoot = xR := by
        ext i
        have h1 : i.1 < k + d := by omega
        simp [embRoot, appendTuple, h1, i.isLt]
      rw [OrientedGraph.pullback_comp, hfun]
    have hL : (H_reg.pullback (appendTuple (appendTuple xR y) z)).pullback embLeft =
        H_reg.pullback (appendTuple xR y) := by
      have hfun : appendTuple (appendTuple xR y) z ∘ embLeft = appendTuple xR y := by
        ext i
        by_cases hi : i.1 < k <;> simp [embLeft, appendTuple, i.isLt, hi]
      rw [OrientedGraph.pullback_comp, hfun]
    have hRt : (H_reg.pullback (appendTuple (appendTuple xR y) z)).pullback embRight =
        H_reg.pullback (appendTuple xR z) := by
      have hfun : appendTuple (appendTuple xR y) z ∘ embRight = appendTuple xR z := by
        ext i
        by_cases hi : i.1 < k
        · have h1 : i.1 < k + d := by omega
          simp [embRight, appendTuple, hi, h1]
        · have h1 : ¬ (i.1 + d < k + d) := by omega
          have hsub : i.1 + d - (k + d) = i.1 - k := by omega
          simp [embRight, appendTuple, hi, h1, hsub]
      rw [OrientedGraph.pullback_comp, hfun]
    unfold sosFactorTerm
    rw [hR, hL, hRt]
    ring
  simp_rw [hfactor, ← Finset.mul_sum, ← Finset.sum_mul]
  have hbase_nn : 0 ≤ tupleWeight w xR * wt * σ_ind (H_reg.pullback xR) :=
    mul_nonneg (mul_nonneg (tupleWeight_nonneg hw xR) hwt) (hσ _)
  exact mul_nonneg hbase_nn (mul_self_nonneg _)

/-! ## Section 4: `Perm (Fin m)` Symmetrization & Master Contradiction Theorem -/

/-- `Perm (Fin m)`-symmetrization of any real function `F` on `OrientedGraph (Fin m)`. -/
def symPerm {m : ℕ} (F : OrientedGraph (Fin m) → ℝ) (H : OrientedGraph (Fin m)) : ℝ :=
  ∑ π : Equiv.Perm (Fin m), F (H.relabel π)

/-- `symPerm F` is invariant under arbitrary vertex relabelings `H.relabel τ`. -/
lemma symPerm_relabel {m : ℕ} (F : OrientedGraph (Fin m) → ℝ)
    (H : OrientedGraph (Fin m)) (τ : Equiv.Perm (Fin m)) :
    symPerm F (H.relabel τ) = symPerm F H := by
  unfold symPerm
  have hmul : ∀ π : Equiv.Perm (Fin m),
      (H.relabel τ).relabel π = H.relabel (τ * π) := fun _ => rfl
  simp_rw [hmul]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => F (H.relabel σ))

/-- Expectation of `symPerm F` equals `|Perm (Fin m)|` times the expectation of `F`, so `0 ≤ E[F]`
implies `0 ≤ E[symPerm F]`. -/
lemma expect_symPerm_nonneg {W : Type u} [Fintype W] {m : ℕ}
    (H_reg : OrientedGraph W) (w : W → ℝ) (F : OrientedGraph (Fin m) → ℝ)
    (hF : 0 ≤ ∑ x : Fin m → W, tupleWeight w x * F (H_reg.pullback x)) :
    0 ≤ ∑ x : Fin m → W, tupleWeight w x * symPerm F (H_reg.pullback x) := by
  unfold symPerm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun π _ => ?_
  rw [sum_tupleWeight_relabel]
  exact hF

/-- **Master Exact Q-SOS Contradiction Theorem**:
If `F : OrientedGraph (Fin m) → ℝ` has non-negative expectation on every `(c_num, c_den)`-regular
`C₃`-free `(H_reg, unifWeight W)` AND `symPerm F H < 0` for every `C₃`-free `OrientedGraph (Fin m)`,
then EVERY finite nonempty simple digraph with minimum out-degree `≥ (c_num / c_den) * |V|`
contains a directed cycle of length `≤ 3`! -/
theorem hasCycleLe3_of_flag_certificate {m c_num c_den : ℕ} (hc_den : 0 < c_den)
    (F : OrientedGraph (Fin m) → ℝ)
    (h_expect_nonneg : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (H_reg : OrientedGraph W) [dH : DecidableRel H_reg.adj],
      H_reg.TriangleFree →
      (∀ u : W, (c_den : ℝ) * @Digraph.outWeight W _ H_reg.toDigraph dH
        (unifWeight W) u = (c_num : ℝ)) →
      0 ≤ ∑ x : Fin m → W, tupleWeight (unifWeight W) x * F (H_reg.pullback x))
    (h_pointwise_neg : ∀ (H : OrientedGraph (Fin m)), H.TriangleFree → symPerm F H < 0) :
    ∀ {V : Type u} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.adj],
      (∀ u : V, ((c_num : ℝ) / (c_den : ℝ)) * (Fintype.card V : ℝ) ≤ (G.outDeg u : ℝ)) →
      G.HasCycleLe3 := by
  intro V _ _ G _ hdeg
  refine hasCycleLe3_of_oriented_bound (c := (c_num : ℝ) / (c_den : ℝ)) ?_ G hdeg
  intro H0 d0 hH0_tri
  by_contra hno
  push Not at hno
  have _ : Nonempty (Fin c_den) := ⟨⟨0, hc_den⟩⟩
  obtain ⟨H_reg, dH, hreg_tri, hreg_deg⟩ :=
    @OrientedGraph.exists_regular_subOrientedGraph_blowup V _ _ H0 d0 hH0_tri c_num c_den hc_den hno
  have h_nn : 0 ≤ ∑ x : Fin m → V × Fin c_den,
      tupleWeight (unifWeight (V × Fin c_den)) x * symPerm F (H_reg.pullback x) :=
    expect_symPerm_nonneg H_reg (unifWeight (V × Fin c_den)) F
      (@h_expect_nonneg (V × Fin c_den) _ _ H_reg dH hreg_tri hreg_deg)
  let hw : IsProbWeight (unifWeight (V × Fin c_den)) := isProbWeight_unifWeight
  let gap : (Fin m → V × Fin c_den) → ℝ := fun x => -symPerm F (H_reg.pullback x)
  have h_pos_all : ∀ x : Fin m → V × Fin c_den, 0 < gap x := fun x =>
    neg_pos.mpr (h_pointwise_neg (H_reg.pullback x) (H_reg.triangleFree_pullback hreg_tri x))
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty gap
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_inf'_iff]
    exact fun x _ => h_pos_all x
  have h_le_neg_δ : ∑ x : Fin m → V × Fin c_den,
      tupleWeight (unifWeight (V × Fin c_den)) x * symPerm F (H_reg.pullback x) ≤ -δ := by
    have h1 : ∀ x ∈ (Finset.univ : Finset (Fin m → V × Fin c_den)),
        tupleWeight (unifWeight (V × Fin c_den)) x * symPerm F (H_reg.pullback x) ≤
          tupleWeight (unifWeight (V × Fin c_den)) x * (-δ) := by
      intro x _
      refine mul_le_mul_of_nonneg_left ?_ (tupleWeight_nonneg hw x)
      have hinf : δ ≤ gap x := Finset.inf'_le gap (Finset.mem_univ x)
      dsimp [gap] at hinf
      linarith
    calc ∑ x : Fin m → V × Fin c_den,
          tupleWeight (unifWeight (V × Fin c_den)) x * symPerm F (H_reg.pullback x)
        ≤ ∑ x : Fin m → V × Fin c_den,
          tupleWeight (unifWeight (V × Fin c_den)) x * (-δ) := Finset.sum_le_sum h1
      _ = (∑ x : Fin m → V × Fin c_den, tupleWeight (unifWeight (V × Fin c_den)) x) * (-δ) := by
          rw [← Finset.sum_mul]
      _ = -δ := by rw [sum_tupleWeight hw, one_mul]
  linarith

end CaccettaHaggkvist
