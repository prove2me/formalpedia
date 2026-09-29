-- Prove2me | solution 1 for lean_workbook_plus_9034
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:10.318302+00:00
-- url     : https://prove2.me/submissions/a0b988d6-651a-4715-979b-a920286787d9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℂ, x^4 + x^3 + (9 / 4) * x^2 + x + 1 - (5 / 4) * x^2 = (x^2 + (1 / 2) * x + 1)^2 - ((Real.sqrt 5 / 2) * x)^2 := by
  intro x
  have hs : ((Real.sqrt 5:ℝ):ℂ)^2=5 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  rw [mul_pow,div_pow,hs]
  ring
