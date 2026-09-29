-- Prove2me | solution 1 for lean_workbook_plus_747
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:44.411988+00:00
-- url     : https://prove2.me/submissions/2c1fa049-00cb-413e-a73f-3347df0f2c36

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (a + b * c) + b / (b + a * c) + c / (c + a * b) ≥ 3 / 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
