-- Prove2me | solution 1 for lean_workbook_plus_29382
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:43.705553+00:00
-- url     : https://prove2.me/submissions/730b74f2-da13-46d3-aa51-74bc17450883

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b + c) ^ 3 ≥ (9 / 4) * (a * (3 * a * b + b * c) + b * (3 * b * c + c * a) + c * (3 * c * a + a * b))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
