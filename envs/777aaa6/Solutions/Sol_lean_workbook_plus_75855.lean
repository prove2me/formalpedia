-- Prove2me | solution 1 for lean_workbook_plus_75855
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:56:59.571065+00:00
-- url     : https://prove2.me/submissions/9fd27812-aa80-4578-ae0c-d0ea2f7685f2

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
theorem solution : ¬ (∀ x y z : ℝ, x^4 * y + x^4 * z + y^4 * z + y^4 * x + z^4 * y + z^4 * x ≤ (1/12) * (x + y + z)^5) := by
  intro h
  have hc := h (-1) (-1) (-1)
  clear h
  norm_num at hc <;> grind only []
