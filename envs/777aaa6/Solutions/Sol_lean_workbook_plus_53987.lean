-- Prove2me | solution 1 for lean_workbook_plus_53987
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:39.09924+00:00
-- url     : https://prove2.me/submissions/d158cd9c-0eb7-477b-b997-3df6f2090cd7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a + b + c = 3 → (3 - a) * (3 - b) * (3 - c) ≥ 8 * a * b * c) := by
  push_neg
  refine ⟨(5), ?_⟩
  refine ⟨(-3/2), ?_⟩
  refine ⟨(-1/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
