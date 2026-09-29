-- Prove2me | solution 1 for lean_workbook_plus_38510
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:22:12.234571+00:00
-- url     : https://prove2.me/submissions/5274e522-710d-43cd-90cd-e926210b210f

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
theorem solution : ¬ (∀ a b c : ℝ, (Real.sqrt (a ^ 2 + (1 - b) ^ 2) + Real.sqrt (b ^ 2 * (1 - c) ^ 2) + Real.sqrt (c ^ 2 + (1 - a) ^ 2)) ≥ (3 * Real.sqrt 2) / 2) := by
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  intro h
  have hc := h 0 0 0
  norm_num at hc
  have hc' : 3 * Real.sqrt 2 / 2 ≤ (2 : ℝ) := by grind only [Real.sqrt_zero, Real.sqrt_one]
  nlinarith only [hc', hs2, hn2]
