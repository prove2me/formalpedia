-- Prove2me | solution 1 for HofmannMoser.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:31:18.810962+00:00
-- url     : https://prove2.me/submissions/796a6b7d-6667-42be-9449-76400ddf67dc

import Definitions.Def_HofmannMoser_Potential

universe u

open HofmannMoser in
theorem solution {C : Nat → Type u} (A : TreeAutomaton C) {n : Nat}
    (c : C n) (vs : Fin n → Value C) (α : Fin A.stateCount) :
    (A.reroot α).basic (.node c vs) =
      (((A.rules n c).filter (fun tr ↦ tr.2 == α)).map fun tr ↦
        (List.ofFn fun i ↦ (A.reroot (tr.1 i)).basic (vs i)).foldl (· * ·) 1).sum := by
  have key : ∀ (q : Fin A.stateCount) (v : Value C) (s : Fin (A.reroot q).stateCount),
      (A.reroot q).runCount v s = A.runCount v s := by
    intro q v
    induction v with
    | node c ch ih =>
      intro s
      rw [TreeAutomaton.runCount.eq_1 (A.reroot q), TreeAutomaton.runCount.eq_1 A s]
      congr 1
      apply List.map_congr_left
      intro tr _
      congr 1
      congr 1
      funext i
      exact ih i (tr.1 i)
  unfold TreeAutomaton.basic
  rw [key]
  rw [TreeAutomaton.runCount.eq_1 A (A.reroot α).final]
  congr 1
  apply List.map_congr_left
  intro tr _
  congr 1
  congr 1
  funext i
  exact (key (tr.1 i) (vs i) (tr.1 i)).symm
