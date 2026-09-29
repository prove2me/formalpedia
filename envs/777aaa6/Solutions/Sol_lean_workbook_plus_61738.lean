-- Prove2me | solution 1 for lean_workbook_plus_61738
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:04:18.515669+00:00
-- url     : https://prove2.me/submissions/2c52191e-4ea5-4d0f-8e6e-86253e4e74de

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
theorem solution : ¬ (∀ a b c : ℝ, (1 / 27) ≥ (a * b * c) / (a + b + c) ^ 3) := by
  intro h
  have hc := h (-1) (-1) 3
  clear h
  norm_num at hc <;> grind only []
