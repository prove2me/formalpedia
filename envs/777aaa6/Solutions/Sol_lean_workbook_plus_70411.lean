-- Prove2me | solution 1 for lean_workbook_plus_70411
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:05.787387+00:00
-- url     : https://prove2.me/submissions/f869ede8-fb2c-48ac-a9fc-c72aaa1d8049

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, (1 - 2 * a) ^ 2 * (3 * a ^ 3 - 6 * a ^ 2 - 2 * a + 8) ≥ 0) := by
  push_neg
  refine ⟨(-2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
