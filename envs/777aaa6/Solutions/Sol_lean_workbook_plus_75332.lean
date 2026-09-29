-- Prove2me | solution 1 for lean_workbook_plus_75332
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:57.682928+00:00
-- url     : https://prove2.me/submissions/2a0cefc5-1c50-486e-a964-cc7ab5a96b88

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
theorem solution : ¬ (∀ x : ℝ, x^2 + (1/x - 1)^2 + 1/(x-1)^2 ≥ 5 ∧ x^2 + (4/x - 1)^2 + 1/(x-1)^2 ≥ 6 ∧ x^2 + (1/x - 1)^2 + (1/x + 1)^2 ≥ 2 * (Real.sqrt 2 + 1)) := by
  push_neg
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith | grind
