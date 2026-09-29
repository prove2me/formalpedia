-- Prove2me | solution 1 for lean_workbook_plus_25475
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:20:37.085677+00:00
-- url     : https://prove2.me/submissions/0028a7cf-7ea2-4282-8418-8e918bf5d93c

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x y : ℝ) (h : x * y = 1), (3 + 2 * x * y) * (18 - 6 * x * y + x ^ 2 * y ^ 2) ≤ 64) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
