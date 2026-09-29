-- Prove2me | solution 1 for lean_workbook_plus_61056
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:42.35173+00:00
-- url     : https://prove2.me/submissions/6d3852c4-8c4e-4c0c-9ee6-3609af054ccd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, x < 1 / 10 → (x^2 + 11 * x + 4) / (3 * x^3 + 7 * x^2 + 5 * x + 1) > 3) := by
  push_neg
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
