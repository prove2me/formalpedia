-- Prove2me | solution 1 for lean_workbook_plus_8277
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:03:25.462229+00:00
-- url     : https://prove2.me/submissions/ea4869e9-d6ef-4f81-a428-dc15d8996564

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
theorem solution : ¬ (∀ a b : ℤ, ¬ 5 ∣ a ∧ ¬ 5 ∣ b → a^3 * b - a * b^3 ≡ 0 [ZMOD 10]) := by
  intro h
  have hc := h 1 2 (by norm_num)
  clear h
  norm_num [Int.ModEq] at hc <;> grind only []
