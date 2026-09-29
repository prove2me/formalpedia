-- Prove2me | solution 1 for lean_workbook_plus_17746
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:11.383694+00:00
-- url     : https://prove2.me/submissions/f9b17600-a1e2-4681-9259-67ee54a649e6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, (a - b) ^ 2 * (2 * a ^ 6 + 5 * a ^ 4 * b ^ 2 + 4 * a ^ 2 * b ^ 4 + b ^ 6 + 10 * a ^ 5 * b + 15 * a ^ 3 * b ^ 3 + 5 * a * b ^ 5 + 26 * a ^ 3 * b ^ 2 + 13 * a * b ^ 4 + 27 * a * b ^ 3) ≥ 0) := by
  push_neg
  refine ⟨(-2/3), (2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
