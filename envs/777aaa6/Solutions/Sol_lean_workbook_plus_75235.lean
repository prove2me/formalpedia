-- Prove2me | solution 1 for lean_workbook_plus_75235
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:23.652195+00:00
-- url     : https://prove2.me/submissions/b99c470b-7485-4515-987a-b580793053fe

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
theorem solution : ¬ (∀ m M : ℝ, ∀ θ : ℝ, (1 / ((1 - θ) * m + θ * M) ≤ (1 - θ) / m + θ / M)) := by
  push_neg
  refine ⟨(0), ?_⟩
  refine ⟨(1/2), ?_⟩
  refine ⟨(2/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
