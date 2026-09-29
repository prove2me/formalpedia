-- Prove2me | solution 1 for lean_workbook_plus_45403
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:03.370975+00:00
-- url     : https://prove2.me/submissions/08a28f8a-7589-478f-9f4e-4bab47451f64

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c d : ℝ, (a / b + b / c + c / d + d / a + 253 / 10 * (a * b + b * c + c * d + d * a + a * c + b * d) / (a + b + c + d) ^ 2) ≥ 1079 / 80) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
