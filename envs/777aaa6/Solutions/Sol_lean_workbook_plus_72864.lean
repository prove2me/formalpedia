-- Prove2me | solution 1 for lean_workbook_plus_72864
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:56.855304+00:00
-- url     : https://prove2.me/submissions/4b74217a-5816-4cc4-9e63-5872629843e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^3 / (a + b) ^ 2 + b^3 / (b + c) ^ 2 + c^3 / (c + a) ^ 2) ≥ (a + b + c) / 4) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
