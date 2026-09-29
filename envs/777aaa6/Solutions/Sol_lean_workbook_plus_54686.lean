-- Prove2me | solution 1 for lean_workbook_plus_54686
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:59.865349+00:00
-- url     : https://prove2.me/submissions/5caa7bfb-0c08-447a-ab57-f31989999b9a

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
theorem solution : ¬ (∀ x y z : ℝ, (x^5 + y^5 + z^5)^6 ≥ 243 * x^6 * y^6 * z^6 * (x^12 + y^12 + z^12)) := by
  push_neg
  refine ⟨(-3/2), ?_⟩
  refine ⟨(-3/2), ?_⟩
  refine ⟨(5/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
