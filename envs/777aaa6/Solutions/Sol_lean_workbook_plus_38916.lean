-- Prove2me | solution 1 for lean_workbook_plus_38916
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:13:40.468983+00:00
-- url     : https://prove2.me/submissions/1b7ab0a4-5da0-4846-9d3e-cde871ca77e1

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
theorem solution : ¬ (∀ k : ℕ, (2 ^ (5 * k) ≡ 1 [ZMOD 5]) ∧ (2 ^ (5 * k + 1) ≡ 2 [ZMOD 5]) ∧ (2 ^ (5 * k + 2) ≡ 4 [ZMOD 5]) ∧ (2 ^ (5 * k + 3) ≡ 3 [ZMOD 5]) ∧ (2 ^ (5 * k + 4) ≡ 1 [ZMOD 5])) := by
  intro h
  have hc := (h 1).1
  clear h
  norm_num [Int.ModEq] at hc <;> grind only []
