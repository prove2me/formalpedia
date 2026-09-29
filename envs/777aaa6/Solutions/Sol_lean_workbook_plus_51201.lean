-- Prove2me | solution 1 for lean_workbook_plus_51201
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:22:34.666713+00:00
-- url     : https://prove2.me/submissions/047ee557-0f67-4932-b854-67e4616a8317

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
theorem solution : ¬ (∀ a b c : ℝ, (1 / 2 : ℝ) ≤ Real.sqrt (a^2 / (4 * a^2 + 5 * b * c)) + Real.sqrt (b^2 / (5 * a * c + 4 * b^2)) + Real.sqrt (c^2 / (5 * a * b + 4 * c^2))) := by
  intro h
  have hc := h 0 0 0
  norm_num at hc <;> grind
