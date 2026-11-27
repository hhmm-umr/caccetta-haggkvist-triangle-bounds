module

public import CaccettaHaggkvist.RazborovSharp

/-! # Vertex deletion and disjoint obstructions to the one-third bound -/

@[expose] public section

namespace CaccettaHaggkvist.OrientedGraph

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def HasCriticalPattern {W : Type*} (G : OrientedGraph W) : Prop :=
  G.HasPattern1 ∨ G.HasPattern2 ∨ G.HasPattern3 ∨ G.HasPattern4

/-- If deleting a transversal of size `k` removes the four patterns, the
degree excess `3d + 1 - n` is at most `2k`. This includes an empty remainder. -/
theorem degree_excess_le_twice_deleted [Nonempty V] (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) {d : ℕ} (hd : ∀ v, d ≤ G.toDigraph.outDeg v)
    (T : Finset V) (hclean : ¬ (G.induce (Finset.univ \ T)).HasCriticalPattern) :
    3 * d + 1 ≤ Fintype.card V + 2 * T.card := by
  let S := Finset.univ \ T
  have hcard : S.card + T.card = Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  by_cases hS : S.Nonempty
  · let _ : Nonempty {v // v ∈ S} := Finset.Nonempty.to_subtype hS
    obtain ⟨w, hw⟩ := (G.induce S).exists_outDeg_le_third_of_forb_4patterns
      (G.triangleFree_induce hG S) (fun h => hclean (Or.inl h))
      (fun h => hclean (Or.inr (Or.inl h))) (fun h => hclean (Or.inr (Or.inr (Or.inl h))))
      (fun h => hclean (Or.inr (Or.inr (Or.inr h))))
    rw [Fintype.card_coe, G.outDeg_induce] at hw
    have hsub : G.toDigraph.outSet w.val \ S ⊆ T := by
      intro y hy
      simpa [S] using (Finset.mem_sdiff.mp hy).2
    have hsum := Finset.card_sdiff_add_card_inter (G.toDigraph.outSet w.val) S
    rw [Finset.inter_comm] at hsum
    have hl := hd w.val
    change d ≤ (G.toDigraph.outSet w.val).card at hl
    have hpos := Finset.card_pos.mpr hS
    have hdel := Finset.card_le_card hsub
    omega
  · have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    let v : V := Classical.choice inferInstance
    have hv := G.toDigraph.notMem_outSet_self v
    have he := Finset.card_le_univ (insert v (G.toDigraph.outSet v))
    rw [Finset.card_insert_of_notMem hv] at he
    have h := hd v
    change d ≤ (G.toDigraph.outSet v).card at h
    omega

omit [Fintype V] in
private theorem small_support (G : OrientedGraph V) {S : Finset V}
    (h : (G.induce S).HasCriticalPattern) :
    ∃ T ⊆ S, T.card ≤ 5 ∧ (G.induce T).HasCriticalPattern := by
  rcases h with h | h | h | h
  all_goals
    obtain ⟨a,b,c,d,e,h⟩ := h
    let T : Finset V := {a.val,b.val,c.val,d.val,e.val}
    have hsub : T ⊆ S := by
      intro z hz
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      all_goals exact Subtype.property _
    have hc : T.card ≤ 5 := by
      dsimp [T]
      calc
        _ ≤ ({b.val,c.val,d.val,e.val} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({c.val,d.val,e.val} : Finset V).card + 2 := by grind [Finset.card_insert_le]
        _ ≤ ({d.val,e.val} : Finset V).card + 3 := by grind [Finset.card_insert_le]
        _ ≤ 5 := by grind [Finset.card_insert_le, Finset.card_singleton]
    refine ⟨T,hsub,hc,?_⟩
    let a' : ↥T := ⟨a.val,by simp [T]⟩
    let b' : ↥T := ⟨b.val,by simp [T]⟩
    let c' : ↥T := ⟨c.val,by simp [T]⟩
    let d' : ↥T := ⟨d.val,by simp [T]⟩
    let e' : ↥T := ⟨e.val,by simp [T]⟩
    simp only [ne_eq, Subtype.ext_iff, induce] at h
    first
    | exact Or.inl ⟨a',b',c',d',e',by simpa only [ne_eq,Subtype.ext_iff,induce] using h⟩
    | exact Or.inr (Or.inl ⟨a',b',c',d',e',by simpa only [ne_eq,Subtype.ext_iff,induce] using h⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨a',b',c',d',e',by simpa only [ne_eq,Subtype.ext_iff,induce] using h⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨a',b',c',d',e',by simpa only [ne_eq,Subtype.ext_iff,induce] using h⟩))

/-- A graph of minimum out-degree `d` contains vertex-disjoint induced
obstructions whose number is at least `⌈(3d+1-n)/10⌉`. -/
theorem exists_disjoint_critical_patterns [Nonempty V] (G : OrientedGraph V) [DecidableRel G.adj]
    (hG : G.TriangleFree) {d : ℕ} (hd : ∀ v, d ≤ G.toDigraph.outDeg v) :
    ∃ P : Finset (Finset V), (∀ T ∈ P, T.card ≤ 5 ∧ (G.induce T).HasCriticalPattern) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      3*d+1 ≤ Fintype.card V + 10*P.card := by
  classical
  let valid (P : Finset (Finset V)) :=
    (∀ T ∈ P, T.card ≤ 5 ∧ (G.induce T).HasCriticalPattern) ∧
    (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B)
  let families := Finset.univ.filter valid
  have hn : families.Nonempty := ⟨∅, by simp [families,valid]⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image families Finset.card hn
  have hp := (Finset.mem_filter.mp hP).2
  let T := P.biUnion id
  have hc : T.card ≤ P.card*5 := by
    calc T.card ≤ ∑ A ∈ P, A.card := Finset.card_biUnion_le
         _ ≤ ∑ _A ∈ P, 5 := Finset.sum_le_sum fun A hA => (hp.1 A hA).1
         _ = P.card * 5 := by simp
  have hclean : ¬ (G.induce (Finset.univ \ T)).HasCriticalPattern := by
    intro h
    obtain ⟨A,hA,h5,ha⟩ := small_support G h
    have dis (B : Finset V) (hb : B ∈ P) : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hz hzB
      exact (Finset.mem_sdiff.mp (hA hz)).2 (Finset.mem_biUnion.mpr ⟨B,hb,hzB⟩)
    have hne : A.Nonempty := by
      rcases ha with h | h | h | h <;> obtain ⟨v, _⟩ := h <;> exact ⟨v.val, v.property⟩
    have hnot : A ∉ P := fun hmem => by
      obtain ⟨v,hv⟩ := hne
      exact Finset.disjoint_left.mp (dis _ hmem) hv hv
    have hnew : insert A P ∈ families := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hb
        · exact ⟨h5,ha⟩
        · exact hp.1 B hb
      · intro B hB C hC hBC
        rcases Finset.mem_insert.mp hB with rfl | hb <;>
          rcases Finset.mem_insert.mp hC with rfl | hc'
        · exact (hBC rfl).elim
        · exact dis _ hc'
        · exact (dis _ hb).symm
        · exact hp.2 B hb C hc' hBC
    have bad := hmax _ hnew
    rw [Finset.card_insert_of_notMem hnot] at bad
    omega
  have bound := G.degree_excess_le_twice_deleted hG hd T hclean
  exact ⟨P,hp.1,hp.2,by omega⟩

end CaccettaHaggkvist.OrientedGraph
