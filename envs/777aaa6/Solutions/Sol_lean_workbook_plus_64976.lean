-- Prove2me | solution 1 for lean_workbook_plus_64976
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:23:55.616001+00:00
-- url     : https://prove2.me/submissions/a690b306-e61c-4ca8-aade-66858bac5ab4

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 2 * a * b * c / (a^3 + b^3 + c^3) ≥ 11 / 3)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
