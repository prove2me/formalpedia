-- Prove2me | solution 1 for lean_workbook_plus_2621
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:46.784135+00:00
-- url     : https://prove2.me/submissions/02db670e-b350-4a44-b284-54fae13dbafb

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
theorem solution : ¬ (∀ x y z : ℝ, (2 / (1 + x ^ 2) - 2 / (1 + y ^ 2) + 3 / (1 + z ^ 2) : ℝ) ≤ 10 / 3) := by
  intro h
  have hc := h 0 1 0
  clear h
  norm_num at hc <;> grind only []
