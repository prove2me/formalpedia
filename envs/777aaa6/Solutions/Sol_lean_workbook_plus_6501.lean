-- Prove2me | solution 1 for lean_workbook_plus_6501
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:49.052655+00:00
-- url     : https://prove2.me/submissions/6778c518-6137-4cd0-8ea6-3a9d8be81ef6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * (a ^ 4 + b ^ 4) * (b ^ 4 + c ^ 4) * (c ^ 4 + a ^ 4) ≥ (a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a * b * c) ^ 4) := by
  push_neg
  refine ⟨(3/4), (-2/3), (-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
