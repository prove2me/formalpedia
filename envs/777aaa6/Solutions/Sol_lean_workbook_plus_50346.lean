-- Prove2me | solution 1 for lean_workbook_plus_50346
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:21.247725+00:00
-- url     : https://prove2.me/submissions/d2f73e27-7382-4fdd-8958-05d2fa4e8090

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
theorem solution : ¬ (∀ a b c : ℝ, (a^3 * b + a^3 * c + b^3 * a + c^3 * a) / 2 ≥ 2 * a^2 * b * c) := by
  push_neg
  refine ⟨(-1/2), ?_⟩
  refine ⟨(-1/2), ?_⟩
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
