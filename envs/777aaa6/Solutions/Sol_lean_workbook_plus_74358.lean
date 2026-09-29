-- Prove2me | solution 1 for lean_workbook_plus_74358
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:22:35.744715+00:00
-- url     : https://prove2.me/submissions/7cfe7421-a6b3-4b23-881c-d7b02a0b06a5

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
theorem solution : ¬ (∀ a b c R s : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ R > 0 ∧ s > 0 →
  Real.sqrt ((a^3 * b^3) / (b + c - a) / (c + a - b)) +
  Real.sqrt ((b^3 * c^3) / (c + a - b) / (a + b - c)) +
  Real.sqrt ((a^3 * c^3) / (a + b - c) / (b + c - a)) ≥
  2 * R * Real.sqrt 3 * s) := by
  have hn3 := Real.sqrt_nonneg (3 : ℝ)
  have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  intro h
  have hc := h 1 1 1 1 10 (by norm_num)
  norm_num at hc
  have hc' : 20 * Real.sqrt 3 ≤ (3 : ℝ) := by grind only [Real.sqrt_one]
  nlinarith only [hc', hs3, hn3]
