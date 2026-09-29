-- Prove2me | solution 1 for lean_workbook_plus_49518
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:27.515709+00:00
-- url     : https://prove2.me/submissions/cffab232-039a-4d1e-b407-d0a5320fe142

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 1 ∧ b > 1 ∧ c > 1 → 2 * b + 2 * c - 3 * b * c - 1 > 0) := by
  push_neg
  refine ⟨(2), ?_⟩
  refine ⟨(2), ?_⟩
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
