-- Prove2me | solution 1 for lean_workbook_plus_1328
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:06.46978+00:00
-- url     : https://prove2.me/submissions/5ebee1f1-4c70-417a-9902-6021e2569a10

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (12 * a * c / (5 * a + 5 * b + 2 * c) + 12 * b * a / (5 * b + 5 * c + 2 * a) + 12 * c * b / (5 * c + 5 * a + 2 * b)) ≤ a + b + c) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
