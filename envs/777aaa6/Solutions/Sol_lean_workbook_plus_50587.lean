-- Prove2me | solution 1 for lean_workbook_plus_50587
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T23:58:06.623755+00:00
-- url     : https://prove2.me/submissions/5c80f615-5f29-49ed-b47e-b0eae4a9a06e

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
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / (a^2 + a * b + b^2) + b^2 / (b^2 + b * c + c^2) + c^2 / (c^2 + c * a + a^2) + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) ≤ 2)) := by
  intro h
  have hc := h 4 (-2) 1
  norm_num at hc <;> grind only []
