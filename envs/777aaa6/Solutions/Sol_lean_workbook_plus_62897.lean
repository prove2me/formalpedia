-- Prove2me | solution 1 for lean_workbook_plus_62897
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:52.383692+00:00
-- url     : https://prove2.me/submissions/e13344a9-d885-4797-8c84-00db6ea8ffa8

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * a * c * (a + c) * (a + b) + 2 * a * b * (b + c) * (a + b) + 2 * b * c * (b + c) * (a + c) - (a + b + c) * (a + b) * (b + c) * (c + a) = 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
