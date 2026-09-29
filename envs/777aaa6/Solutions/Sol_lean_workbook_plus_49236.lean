-- Prove2me | solution 1 for lean_workbook_plus_49236
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:10.044932+00:00
-- url     : https://prove2.me/submissions/4334a761-b766-4f02-a2d5-33a352e613b0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ≥ a^3 * b * c + b^3 * a * c + c^3 * a * b) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
