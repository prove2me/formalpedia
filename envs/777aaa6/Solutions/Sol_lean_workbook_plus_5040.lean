-- Prove2me | solution 1 for lean_workbook_plus_5040
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:37:24.590321+00:00
-- url     : https://prove2.me/submissions/0a811f94-6f3c-49f9-a132-8d89990fecd9

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
theorem solution : ¬ (∀ x ≥ 0, 14 + Real.sqrt (2 - x ^ 2) ≥ |x ^ 4 - 9 * x ^ 2|) := by
  intro h
  have hc := h 4 (by norm_num)
  norm_num [Real.sqrt_eq_zero_of_nonpos] at hc <;> grind only []
