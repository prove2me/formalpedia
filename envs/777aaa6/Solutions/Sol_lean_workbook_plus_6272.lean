-- Prove2me | solution 1 for lean_workbook_plus_6272
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:23.015713+00:00
-- url     : https://prove2.me/submissions/ff2c3af3-633d-408d-86d0-8c289d0ac1c6

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x ^ 3 + y ^ 3 + z ^ 3) ^ 8 ≥ 243 * (x ^ 4 * y ^ 4 + x ^ 4 * z ^ 4 + y ^ 4 * z ^ 4) ^ 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
