-- Prove2me | solution 1 for lean_workbook_plus_41244
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:05:47.569691+00:00
-- url     : https://prove2.me/submissions/5953be80-9525-4fde-8511-1ba8c9a950e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 → a * b * c = 1 → 1 / a + 1 / b + 1 / c + 3 / (a + b + c) ≥ 8 / 3 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) := by
  push_neg
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
