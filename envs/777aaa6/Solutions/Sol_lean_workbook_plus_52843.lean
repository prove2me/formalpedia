-- Prove2me | solution 1 for lean_workbook_plus_52843
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:54.821055+00:00
-- url     : https://prove2.me/submissions/8f0939dc-0128-4108-8c86-6dda43cef46b

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
theorem solution : ¬ (∀ a b c : ℝ, (1 / b + 1 / c + 1 / a) * ((a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - a) ^ 2 / a) ≥ ((a - b) / b + (b - c) / c + (c - a) / a) ^ 2) := by
  push_neg
  refine ⟨(-4), ?_⟩
  refine ⟨(3), ?_⟩
  refine ⟨(-3/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
