-- Prove2me | solution 1 for lean_workbook_plus_9391
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:29.692962+00:00
-- url     : https://prove2.me/submissions/a4c020cd-8718-4cbd-90e8-8d56cb216377

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
theorem solution : ¬ (∀ x y : ℝ, 12*(x-y)^2*(x^4+y^4+x^3*y+x*y^3+x^2*y^2) - 13*x^2*y^2*(x-y)^2 ≥ 0) := by
  push_neg
  refine ⟨(3/2), ?_⟩
  refine ⟨(-3/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
