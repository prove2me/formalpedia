-- Prove2me | solution 1 for lean_workbook_plus_31223
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:02.618308+00:00
-- url     : https://prove2.me/submissions/a46dcd7c-f330-462a-b07e-22987252908a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ k l m n p : ℝ, (Real.sqrt ((k + l) ^ 2 + (m + n) ^ 2 + (k + l + m + n) ^ 2) + Real.sqrt ((l + m) ^ 2 + (n + p) ^ 2 + (l + m + n + p) ^ 2)) ^ 2 > 2 * (k + m + p) ^ 2) := by
  push_neg
  refine ⟨(0), (0), (0), (0), (0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
