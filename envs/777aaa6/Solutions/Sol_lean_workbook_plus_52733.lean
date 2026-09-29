-- Prove2me | solution 1 for lean_workbook_plus_52733
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:20.896897+00:00
-- url     : https://prove2.me/submissions/8fb26d09-57c2-4c28-906a-73e74940af2c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (2 + a * b * c) / (1 + a * b * c) + a * b * c ≤ 5 / 2 ↔ (1 + 2 * a * b * c) * (1 - a * b * c) ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
