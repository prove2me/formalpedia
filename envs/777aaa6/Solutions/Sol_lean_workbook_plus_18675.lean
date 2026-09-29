-- Prove2me | solution 1 for lean_workbook_plus_18675
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:51.874287+00:00
-- url     : https://prove2.me/submissions/f43e1f09-9514-456c-81e1-0791ced76251

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 4 * (y * z + z * x + x * y) ^ 3 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x + x * y * z) ^ 2 ≥ 27 * x ^ 2 * y ^ 2 * z ^ 2 * (y + z) ^ 2 * (z + x) ^ 2 * (x + y) ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
