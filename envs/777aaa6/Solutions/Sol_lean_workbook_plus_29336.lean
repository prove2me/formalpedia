-- Prove2me | solution 1 for lean_workbook_plus_29336
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:30.900261+00:00
-- url     : https://prove2.me/submissions/890b2f52-bc40-41ad-9c73-4b1995cc099f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, 2 * a ^ 2 + 2 * b ^ 2 ≥ 2 * a ^ 2 * b + 2 * a * b + (a - b) ^ 2 * (a + b)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
