-- Prove2me | solution 1 for lean_workbook_plus_39376
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:13.097269+00:00
-- url     : https://prove2.me/submissions/c904edca-d65a-4b11-a741-08d2ed2d24a4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 0), -2 * x ^ 2 - 2 * x + 2 ≤ 5 / 4) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
