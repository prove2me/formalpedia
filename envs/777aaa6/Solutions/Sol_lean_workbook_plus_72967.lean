-- Prove2me | solution 1 for lean_workbook_plus_72967
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:04.031222+00:00
-- url     : https://prove2.me/submissions/f693513d-553d-423d-a3d4-8f0998a3ddf9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (b ^ 2 + c ^ 2) + b / (c ^ 2 + a ^ 2) + c / (a ^ 2 + b ^ 2) ≥ 4 / 5 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) + 81 * a * b * c / (10 * (a + b + c) ^ 2 * (a * b + b * c + c * a)))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
