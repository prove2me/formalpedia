-- Prove2me | solution 1 for lean_workbook_plus_48129
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:42.130581+00:00
-- url     : https://prove2.me/submissions/19692806-ec3d-48c3-8751-ac4a0dc909cc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^2 + b^2 + c^2 + (9 * a * b * c) / (a + b + c) ≥ 2 * (a * b + b * c + c * a)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
