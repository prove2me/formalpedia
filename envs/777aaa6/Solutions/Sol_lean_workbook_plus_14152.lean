-- Prove2me | solution 1 for lean_workbook_plus_14152
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:06.462133+00:00
-- url     : https://prove2.me/submissions/bc683010-8869-4714-9f08-4b1d7adff036

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / (a^2 + 2 * b * c) + b^2 / (b^2 + 2 * c * a) + c^2 / (c^2 + 2 * a * b) ≥ (a + b + c) ^ 2 / (3 * (a * b + b * c + a * c)))) := by
  push_neg
  refine ⟨(3), ?_⟩
  refine ⟨(-10), ?_⟩
  refine ⟨(5), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
