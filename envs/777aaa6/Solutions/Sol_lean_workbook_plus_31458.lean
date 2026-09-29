-- Prove2me | solution 1 for lean_workbook_plus_31458
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:36:12.906384+00:00
-- url     : https://prove2.me/submissions/71f776e7-b3ba-4f3b-9a08-e1267ee4b7ca

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ^ 3 + b ^ 3 + c ^ 3 ≠ (a + b + c) * (a ^ 2 - b ^ 2 - c ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
