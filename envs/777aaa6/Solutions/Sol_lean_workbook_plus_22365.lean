-- Prove2me | solution 1 for lean_workbook_plus_22365
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:01.691377+00:00
-- url     : https://prove2.me/submissions/d2adc5e1-24d4-4c65-9929-70ae618053ba

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^3 * (a + b) / (a^2 + b^2) + b^3 * (b + c) / (b^2 + c^2) + c^3 * (c + a) / (c^2 + a^2)) ≥ a^2 + b^2 + c^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
