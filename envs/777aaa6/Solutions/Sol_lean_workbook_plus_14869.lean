-- Prove2me | solution 1 for lean_workbook_plus_14869
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:08:24.086272+00:00
-- url     : https://prove2.me/submissions/fee043d8-2d90-4a83-b66f-44291fc64bba

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x₁ x₂ x₃ : ℝ, (x₁ + x₂ + x₃) ^ 2 ≥ 9 + 3 * x₃ * (x₁ + x₂ + x₃ - 3) + 2 * x₁ * x₂ - 2 * x₃ ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
