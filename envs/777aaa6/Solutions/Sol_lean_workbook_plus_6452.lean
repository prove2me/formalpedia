-- Prove2me | solution 1 for lean_workbook_plus_6452
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:38.232883+00:00
-- url     : https://prove2.me/submissions/effabc7e-b376-400a-87c1-89324526232a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y : ℝ, (x - y) ^ 2 * (x ^ 2 * y ^ 3 + 2 * x + y) / y ^ 3 ≥ 0) := by
  push_neg
  refine ⟨(-3/2), (2/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
