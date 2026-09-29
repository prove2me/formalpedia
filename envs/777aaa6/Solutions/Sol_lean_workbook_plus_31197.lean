-- Prove2me | solution 1 for lean_workbook_plus_31197
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:34.779317+00:00
-- url     : https://prove2.me/submissions/495dc786-0f2e-4537-b62b-210032ddb618

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) + 1 / (b ^ 4 + b ^ 2 * c ^ 2 + c ^ 4) + 1 / (c ^ 4 + c ^ 2 * a ^ 2 + a ^ 4)) ≥ 9 / ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
