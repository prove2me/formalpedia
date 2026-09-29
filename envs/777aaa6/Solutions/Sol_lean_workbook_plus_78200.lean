-- Prove2me | solution 1 for lean_workbook_plus_78200
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:22:04.405544+00:00
-- url     : https://prove2.me/submissions/2e0ca332-2cbc-4a2b-b111-c200e9e843d2

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
theorem solution : ¬ (∀ (n : ℕ) (hn : n ≡ 4 [ZMOD 8]) (p : ℕ) (hp : p.Prime) (h : p ∣ (n + 2)), n ≡ 3 [ZMOD 4]) := by
  intro h
  have hc := h 4 (by norm_num [Int.ModEq]) 2 (by norm_num) (by norm_num)
  clear h
  norm_num [Int.ModEq] at hc <;> grind only []
