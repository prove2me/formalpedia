-- Prove2me | solution 1 for lean_workbook_plus_13998
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:09:05.445584+00:00
-- url     : https://prove2.me/submissions/d3e5c901-8d86-4e49-9f9a-0e2a4c226d2e

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + 1) ^ (-2:ℤ) + (b + 1) ^ (-2:ℤ) + (c + 1) ^ (-2:ℤ) + (a + b + c) / 4 ≥ 3 / 2) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
