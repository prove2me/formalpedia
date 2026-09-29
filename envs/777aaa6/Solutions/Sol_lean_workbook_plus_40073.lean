-- Prove2me | solution 1 for lean_workbook_plus_40073
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:52.862018+00:00
-- url     : https://prove2.me/submissions/e3db8aec-ffc6-435a-bb70-eb99b6f0e15d

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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, (x - (1 / 2 * Complex.I))^5 = (x + (1 / 2 * Complex.I))^5) := by
  intro h
  have hc := congrArg Complex.im (h 0)
  clear h
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im] at hc <;> grind only []
