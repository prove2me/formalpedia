-- Prove2me | solution 1 for lean_workbook_plus_15689
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:40.493789+00:00
-- url     : https://prove2.me/submissions/f84c6514-71ab-4883-82c3-9f9d36c8b730

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (1 + a) ^ 3 + b / (1 + b) ^ 3 + c / (1 + c) ^ 3 ≤ 3 / 8) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
