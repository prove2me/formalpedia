-- Prove2me | solution 1 for lean_workbook_plus_23287
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:38.073733+00:00
-- url     : https://prove2.me/submissions/5d89b591-fbbe-46dc-904f-338772ce6efe

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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n : ℕ, Even n ∧ n > 0 → (2^n - 1 ≡ 1 [ZMOD 3])) := by
  intro h
  have hc := h 2 (by norm_num)
  clear h
  norm_num [Int.ModEq] at hc <;> grind only []
