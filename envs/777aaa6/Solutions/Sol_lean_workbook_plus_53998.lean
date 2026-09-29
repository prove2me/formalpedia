-- Prove2me | solution 1 for lean_workbook_plus_53998
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:03:26.468858+00:00
-- url     : https://prove2.me/submissions/cb4a10ae-2847-40ca-ba4c-c8f5e02bb8f6

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
theorem solution : ¬ (∀ a b : ℝ, (a + b - 2) * (a + b + 6) ≥ 0 → a + b ≥ 2) := by
  intro h
  have hc := h (-6) 0 (by norm_num)
  clear h
  norm_num at hc <;> grind only []
