-- Prove2me | solution 1 for lean_workbook_plus_28226
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:22:38.236711+00:00
-- url     : https://prove2.me/submissions/f5cfba0f-fbfc-4a85-8c47-b25ef5a0d621

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
theorem solution : ¬ (∀ a b c : ℝ, 3 * Real.sqrt (4 * a ^ 2 + 4 * b ^ 2 + 4 * c ^ 2 + 6 * a * b * c) ≤ Real.sqrt (15 * a ^ 3 + 1) + Real.sqrt (15 * b ^ 3 + 1) + Real.sqrt (15 * c ^ 3 + 1)) := by
  have hn6 := Real.sqrt_nonneg (6 : ℝ)
  have hs6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  intro h
  have hc := h (-1) (-1) (-1)
  norm_num [Real.sqrt_eq_zero_of_nonpos] at hc
  have hc' : 3 * Real.sqrt 6 ≤ (0 : ℝ) := by grind only []
  nlinarith only [hc', hs6, hn6]
