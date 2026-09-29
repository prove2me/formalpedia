-- Prove2me | solution 1 for lean_workbook_plus_49234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:21.544253+00:00
-- url     : https://prove2.me/submissions/230192db-748e-4656-a431-00b65f810d63

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a^2 + b^2 + c^2 + 2 * a * b + 2 * a * c + 2 * b * c = (a + b + c)^2 ∧ (a + b + c)^2 ≥ 0 := by
  intro a b c
  intros
  repeat constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
