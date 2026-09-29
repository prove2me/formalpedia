-- Prove2me | solution 1 for lean_workbook_plus_61552
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:44.564223+00:00
-- url     : https://prove2.me/submissions/a068371e-31b8-4ea0-b7fb-9c654cf4de1c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ^ 5 + b ^ 5 + c ^ 5 ≥ (1 / 27) * (a + b + c) ^ 3 * (a ^ 2 + b ^ 2 + c ^ 2) ∧ (1 / 27) * (a + b + c) ^ 3 * (a ^ 2 + b ^ 2 + c ^ 2) >= a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
