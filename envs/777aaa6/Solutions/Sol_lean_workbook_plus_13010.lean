-- Prove2me | solution 1 for lean_workbook_plus_13010
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:20.265026+00:00
-- url     : https://prove2.me/submissions/8424ac7f-fbae-4d5e-9d5c-d831728f0b03

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a * b + c) / (a * b + 2 * c + 3) + (b * c + a) / (b * c + 2 * a + 3) + (c * a + b) / (c * a + 2 * b + 3) ≤ (a + b + c + 3) / 6) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
