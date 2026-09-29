-- Prove2me | solution 1 for lean_workbook_plus_65053
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:52.881136+00:00
-- url     : https://prove2.me/submissions/1209ca58-8b5b-4db9-a741-3543511f8574

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
theorem solution : ¬ (∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 ≥ (a ^ 3 * b + b ^ 3 * a) + (c ^ 3 * a + a ^ 3 * c) + (b * c ^ 3 + c * b ^ 3) ∧ (a ^ 3 * b + b ^ 3 * a) + (c ^ 3 * a + a ^ 3 * c) + (b * c ^ 3 + c * b ^ 3) ≥ 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
