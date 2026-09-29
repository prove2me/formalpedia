-- Prove2me | solution 1 for lean_workbook_plus_35232
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:00:02.421848+00:00
-- url     : https://prove2.me/submissions/aacb9e5e-8dea-426b-826e-cf26011e45d7

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 8 * a * b * c / (a + b) / (b + c) / (c + a) ≥ 2) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
