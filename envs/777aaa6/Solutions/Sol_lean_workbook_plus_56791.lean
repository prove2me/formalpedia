-- Prove2me | solution 1 for lean_workbook_plus_56791
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:39:00.204783+00:00
-- url     : https://prove2.me/submissions/57a5c6d8-3f55-4c3f-b215-86e7a77805f2

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a + b + c = 1 → 4 * (a * b + b * c + c * a) - 9 * a * b * c ≤ 1) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
