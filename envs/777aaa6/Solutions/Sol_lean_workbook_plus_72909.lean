-- Prove2me | solution 1 for lean_workbook_plus_72909
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:44.936435+00:00
-- url     : https://prove2.me/submissions/792c0d8c-8dfc-45c6-b4f4-849241a5f0f9

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
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 1 / 2 + 1 / 2 * Real.sqrt ((a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) ≤ Real.sqrt (a ^ 2 / (4 * a ^ 2 + 5 * b * c)) + Real.sqrt (b ^ 2 / (5 * c * a + 4 * b ^ 2)) + Real.sqrt (c ^ 2 / (5 * a * b + 4 * c ^ 2))) := by
  intro h
  have hc := h 0 0 0
  norm_num at hc <;> grind
