-- Prove2me | solution 1 for lean_workbook_plus_74732
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:03:14.597059+00:00
-- url     : https://prove2.me/submissions/4c7815fa-7a34-4a18-a380-777cee12e56c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y : ℝ, (x / (y + 3) + 2 * y / (x + 1) ≥ 1 / 5 ↔ 4 * x ^ 2 - 12 * x + 9 ≥ 0)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
