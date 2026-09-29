-- Prove2me | solution 1 for lean_workbook_plus_12070
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:46.893254+00:00
-- url     : https://prove2.me/submissions/8c8a848d-fdf0-4240-b3db-6eaec01fc423

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c d : ℝ, (a * b ^ 2 + b * c ^ 2 + c * d ^ 2 + a ^ 2 * d) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * d + d ^ 2 * a) ≥ (a * c * d + a * b * d + b * c * a + b * d * c) ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
