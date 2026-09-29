-- Prove2me | solution 1 for lean_workbook_plus_29581
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:30.926653+00:00
-- url     : https://prove2.me/submissions/1fba545f-e100-4e39-ad22-cddc2a1295b0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^2 + b^2 + c^2 + (a * b * c * (a + b + c)^2) / (a^2 * b + b^2 * c + c^2 * a) ≥ 2 * (a * b + b * c + c * a)) := by
  push_neg
  refine ⟨(-1), (-3/2), (1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
