-- Prove2me | solution 1 for lean_workbook_plus_3518
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:11:53.847058+00:00
-- url     : https://prove2.me/submissions/12f6aa56-6885-4c8d-980b-95544360e311

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
theorem solution : ¬ (∀ a b c : ℝ, (c / (a + c))^3 + (a / (a + b))^3 + (b / (b + c))^3 ≤ 9 / 8) := by
  push_neg
  refine ⟨(1/4), ?_⟩
  refine ⟨(-3), ?_⟩
  refine ⟨(5/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
