-- Prove2me | solution 1 for LinearOptimization.lp_dual_dual
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T21:58:57.061596+00:00
-- url     : https://prove2.me/submissions/d0f793b1-c8bf-4bd5-877e-04dda5ea0f63

import Definitions.Def_LinearOptimization_DualLP

open Matrix LinearOptimization

theorem solution {m n : ℕ} (P : GeneralFormLP m n) :
    dualLP (dualLP P) = P := by
  cases P with
  | mk A b c rowRel colSign =>
    simp only [dualLP, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg,
      GeneralFormLP.mk.injEq, true_and]
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩
    · cases rowRel i <;> rfl
    · cases colSign j <;> rfl
