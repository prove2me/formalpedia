-- Prove2me | solution 1 for lean_workbook_plus_55646
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:14.990211+00:00
-- url     : https://prove2.me/submissions/1dde3e00-f9ec-4cb7-9308-427bcadeea40

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y : ℝ, (x ≠ 0 ∧ y ≠ 0) → 1 / x ^ 2 + 4 / y ^ 2 ≥ 2 * (1 / x + 1 / y)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  linarith
