-- Prove2me | solution 1 for lean_workbook_plus_10325
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:51.516103+00:00
-- url     : https://prove2.me/submissions/828cc0cc-7d15-48bd-8ae2-873d1b6895e2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, (a + b) * (a ^ 3 + b ^ 3) ^ 2 ≥ (a ^ 2 + b ^ 2) ^ 2 * (a ^ 3 + b ^ 3)) := by
  push_neg
  refine ⟨(3/4), (-1/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
