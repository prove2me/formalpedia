-- Prove2me | solution 1 for lean_workbook_plus_39610
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:09.328719+00:00
-- url     : https://prove2.me/submissions/92343ca7-8ccf-4254-b838-2aa8947b1450

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + 3 * b * c) / (b + c)^2 + (b^2 + 3 * c * a) / (c + a)^2 + (c^2 + 3 * a * b) / (a + b)^2 + 13 / 12 ≥ (49 / 4) * (a * b + b * c + c * a) / (a + b + c)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
