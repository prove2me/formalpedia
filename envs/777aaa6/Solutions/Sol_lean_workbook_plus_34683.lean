-- Prove2me | solution 1 for lean_workbook_plus_34683
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:06:36.609244+00:00
-- url     : https://prove2.me/submissions/a3e2726e-215e-472c-accd-6149a0b053d7

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 2 * x * y + 2 * x * z + 2 * y * z ≤ (z + x * y) * (x + y * z) / (z + x) + (y + x * z) * (x + y * z) / (x + y) + (z + x * y) * (y + x * z) / (y + z)) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ -  1 , ?_⟩
  norm_num
  refine ⟨ 2 , ?_⟩
  norm_num
