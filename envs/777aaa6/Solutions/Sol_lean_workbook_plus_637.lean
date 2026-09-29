-- Prove2me | solution 1 for lean_workbook_plus_637
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:55.259579+00:00
-- url     : https://prove2.me/submissions/414d7e13-4dbc-4668-87f2-455ed84c39e6

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
theorem solution : ¬ (∀ a b c : ℝ, a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a)) := by
  intro h
  have hc := h (-1) (-1) (-1)
  clear h
  norm_num at hc <;> grind only []
