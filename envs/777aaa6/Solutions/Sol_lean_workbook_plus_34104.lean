-- Prove2me | solution 1 for lean_workbook_plus_34104
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:09.133564+00:00
-- url     : https://prove2.me/submissions/31e8114e-ce8c-438e-9849-dbbb7824d0a9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ t : ℝ, -1 / 81 * (t - 3) * (t ^ 4 + 3 * t ^ 3 + 27 * t ^ 2 + 81 * t + 324) ≥ 0) := by
  push_neg
  refine ⟨(4), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
