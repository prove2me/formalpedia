-- Prove2me | solution 1 for lean_workbook_plus_47112
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:07:07.718706+00:00
-- url     : https://prove2.me/submissions/f66c68b2-b220-496b-b1f4-3ff11e363f2a

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 2 ≥ (2 / 3) * (a / (b + c) + b / (c + a) + c / (a + b))) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num
  refine ⟨ -  2 , ?_⟩
  norm_num
