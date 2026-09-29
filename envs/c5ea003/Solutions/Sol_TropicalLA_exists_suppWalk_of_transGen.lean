-- Prove2me | solution 1 for TropicalLA.exists_suppWalk_of_transGen
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T09:16:08.88327+00:00
-- url     : https://prove2.me/submissions/72f9224c-b43f-4c0f-8db8-3c3b642a0c27

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} {A : Matrix ι ι (WithBot ℝ)} {i j : ι}
    (h : Relation.TransGen (Supp A) i j) :
    ∃ (m : ℕ) (p : ℕ → ι), 0 < m ∧ p 0 = i ∧ p m = j ∧ IsSuppWalk A p m := by
  induction h with
  | single hij =>
    -- a single support edge is a walk of length one
    rename_i b
    refine ⟨1, fun t => if t = 0 then i else b, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t ht
    interval_cases t
    simpa using hij
  | @tail k c hik hkc ih =>
    -- extend the walk by one edge, keeping the old prefix
    obtain ⟨m, p, hm, hp0, hpm, hwalk⟩ := ih
    refine ⟨m + 1, fun t => if t ≤ m then p t else c, by omega, ?_, ?_, ?_⟩
    · simp [hp0]
    · simp
    · intro t ht
      by_cases htm : t < m
      · have h1 : t ≤ m := by omega
        have h2 : t + 1 ≤ m := by omega
        simp only [if_pos h1, if_pos h2]
        exact hwalk t htm
      · have hte : t = m := by omega
        subst hte
        simp only [if_pos (le_refl t), if_neg (by omega : ¬ (t + 1 ≤ t))]
        rw [hpm]
        exact hkc
