-- Prove2me | solution 1 for lean_workbook_plus_21717
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:08.527297+00:00
-- url     : https://prove2.me/submissions/751571b8-dde1-4798-bd56-c8fa3367d9e1

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
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → a / (a + b * c) + c / (b + a * c) + b / (c + a * b) ≤ 9 / 4) := by
  intro h
  have hc := h (1/4) (1/2) (1/4) (by norm_num)
  clear h
  norm_num at hc <;> grind only []
