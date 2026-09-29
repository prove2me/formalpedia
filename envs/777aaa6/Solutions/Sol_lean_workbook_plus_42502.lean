-- Prove2me | solution 1 for lean_workbook_plus_42502
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:30:39.220553+00:00
-- url     : https://prove2.me/submissions/8f833b98-0f8f-4810-be94-cf2d27a0f53a

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, (2 * (a + b + 1) ^ 2 / (a ^ 2 + b ^ 2 + 3 * a * b + 3 * a + 3 * b + 1) ≥ 3 / 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
