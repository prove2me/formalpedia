-- Prove2me | solution 1 for lean_workbook_plus_65997
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:06.697469+00:00
-- url     : https://prove2.me/submissions/b50875c1-06bd-4913-a0f5-b8ce43567424

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
theorem solution : ¬ (∀ a b c : ℝ, (a * b + b * c + c * a) / (a + b) = (a * b / (a + b)) + c ∧ (a * b / (a + b)) + c ≤ (a + b) / 4 + c) := by
  push_neg
  refine ⟨(-1), ?_⟩
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
