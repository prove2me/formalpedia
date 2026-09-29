-- Prove2me | solution 1 for lean_workbook_plus_27050
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:02.273499+00:00
-- url     : https://prove2.me/submissions/37296184-67c1-45cf-955b-a8cdcaaec2aa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a + b + c = 1 → 1 / (6 * a ^ 2 + 1) + 1 / (6 * b ^ 2 + 1) + 1 / (6 * c ^ 2 + 1) ≥ 9 / 5) := by
  push_neg
  refine ⟨(-5), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(5), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
