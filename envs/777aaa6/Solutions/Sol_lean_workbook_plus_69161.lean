-- Prove2me | solution 1 for lean_workbook_plus_69161
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:25.366937+00:00
-- url     : https://prove2.me/submissions/2dd1b900-827b-43c3-8422-6cea7870c96b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 * b + b^2 * c + c^2 * a) * (a * b / c + b * c / a + c * a / b)^2 ≥ (3 * a * b * c)^2 * (1 / a + 1 / b + 1 / c)) := by
  push_neg
  refine ⟨(1/4), (3/4), (-1/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
