-- Prove2me | solution 1 for lean_workbook_plus_920
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:47.068627+00:00
-- url     : https://prove2.me/submissions/a1509a70-8c6a-4d6c-b93f-c6c1fe89624e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c d k : ℝ, k < 3 → 2 * (a * b + b * c + c * d + d * a + a * c + b * d) ≤ a + b + c + d + k * (a * b * c + a * b * d + a * c * d + b * c * d)) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
