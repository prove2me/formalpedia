-- Prove2me | solution 1 for lean_workbook_plus_5807
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:45.065919+00:00
-- url     : https://prove2.me/submissions/8c9fe81a-8406-4ec1-b1f2-6706c57c2f9c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, a > 0 ∧ b > 0 → a^2 + b^2 + b^2 / a^2 ≥ a / b + b / a) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
