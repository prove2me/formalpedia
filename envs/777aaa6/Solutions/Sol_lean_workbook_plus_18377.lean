-- Prove2me | solution 1 for lean_workbook_plus_18377
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:28.870319+00:00
-- url     : https://prove2.me/submissions/75ec992d-e154-4b21-b35a-7a785f896028

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1/2 * a^3 + 1/2 * b^3 + 1/2 * c^3 + 9/2 * b * c * a) ≤ (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
