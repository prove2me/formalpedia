-- Prove2me | solution 1 for Novelty.MirrorBridge.dualMon_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:48:14.556376+00:00
-- url     : https://prove2.me/submissions/f1d0a680-866a-46dc-a7f4-fafbdb019571

import Mathlib
import Definitions.Def_Novelty_SYZMonodromyDuality
import Definitions.Def_Novelty_SYZDualityRankN
open Novelty.MirrorBridge in
theorem solution (M : IntGL 1) : dualMon M = M := by
  have hvi : M.val * M.inv = 1 := M.val_inv
  have h00 : M.val 0 0 * M.inv 0 0 = 1 := by
    have h := congrFun (congrFun hvi 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply] using h
  have heq : M.inv 0 0 = M.val 0 0 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h00 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  refine Units.ext ?_
  ext i j
  fin_cases i
  fin_cases j
  simp only [dualMon, Matrix.transpose_apply]
  exact heq
