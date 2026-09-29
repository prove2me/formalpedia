-- Prove2me | solution 1 for lean_workbook_plus_14251
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:15.24575+00:00
-- url     : https://prove2.me/submissions/0f5b44d7-55d3-4b17-8b82-9ca5cee465d3

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
theorem solution : ¬ (∀ a b c : ℝ, a + b + c = 1 → a * b * (3 * a - 1) + a * c * (3 * b - 1) + b * c * (3 * c - 1) ≥ 0) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(-1/2), ?_⟩
  refine ⟨(1/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
