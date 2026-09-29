-- Prove2me | solution 1 for lean_workbook_plus_28716
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:12.474234+00:00
-- url     : https://prove2.me/submissions/f1181346-27f4-46c4-9902-cb27fd8bac7a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 6 * a * b * c < a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ∧ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) < 2 * (a ^ 3 + b ^ 3 + c ^ 3)) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
