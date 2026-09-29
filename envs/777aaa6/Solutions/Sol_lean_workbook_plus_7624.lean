-- Prove2me | solution 1 for lean_workbook_plus_7624
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:36.500059+00:00
-- url     : https://prove2.me/submissions/33dda1eb-9cd6-486f-941b-dc3e2d529730

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x * y + y * z + z * x) ^ 2 - 3 / 2 * x * y * z * (x + y + z) ≤ 1 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + y * z + z * x)) := by
  push_neg
  refine ⟨(-3), (2/3), (1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
