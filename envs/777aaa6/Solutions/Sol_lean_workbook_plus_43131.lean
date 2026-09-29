-- Prove2me | solution 1 for lean_workbook_plus_43131
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:12:47.832813+00:00
-- url     : https://prove2.me/submissions/348d1dee-3f0f-4818-8509-8693ba621b55

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, (2 * x ^ 2 - 2 * x ^ 3) ^ 2 * (5 * x - 2) = ((2 * x - 1) * (5 * x ^ 3 - x ^ 2) - 2 * x ^ 2 * (1 + x)) ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
