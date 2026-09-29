-- Prove2me | solution 1 for lean_workbook_plus_74688
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:52.744567+00:00
-- url     : https://prove2.me/submissions/1a97e84b-0c91-486e-a8c8-9eae992505b6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a + b + c = 1 → a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 >= 9 / 4) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
