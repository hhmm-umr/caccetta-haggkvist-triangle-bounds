module

public import CaccettaHaggkvist.SixVertexReflection
public import CaccettaHaggkvist.IntervalM6Bridge

@[expose] public section

namespace CaccettaHaggkvist.SixVertex

/-- A compiled certificate needs only a valid permutation table, the finite
Gram checks and the reflected model rows. There is no graph-expectation premise. -/
theorem cStar_le_of_program (P : Program) (E : Endpoints) {table : ℕ}
    (ht : checkPermutations table = true) (hp : P.check = true)
    (hl : 0 < E.loDen) (hh : 0 < E.hiDen) (hupper : cStar ≤ (E.hiNum : ℝ)/E.hiDen)
    (rows : ∀ i : Fin 6583, E.accepts (modelRow P table (models6Tree.get i.val)) = true) :
    cStar ≤ (E.loNum : ℝ)/E.loDen := by
  let U := fun K => ((P.score K).1 : ℝ)
  let V := fun K => ((P.score K).2 : ℝ)
  apply cStar_le_of_six_vertex_interval hupper P.loss_nonneg U V
  · intro n hn c ε hε G d hG hreg hhered
    let _ : DecidableRel G.adj := d
    exact P.expectation_ge hp hn G hG hε.le hreg hhered
  · intro i
    change symPerm (fun K => atRatio (P.score K) _) _ ≤ 0 ∧
      symPerm (fun K => atRatio (P.score K) _) _ < 0
    rw [modelRow_spec P ht, modelRow_spec P ht]
    exact E.correct hl hh (rows i)

end CaccettaHaggkvist.SixVertex
