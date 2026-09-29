-- Prove2me | solution 1 for lean_workbook_plus_43160
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:54.652753+00:00
-- url     : https://prove2.me/submissions/ab5b2da6-2078-4bc8-a6c7-2fd240815046

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
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) + a + b + c) ≥ (3 / 2) * Real.sqrt (3 * (a^2 + b^2 + c^2))) := by
  intro h
  have hc := h (-1) (-1) (-1)
  norm_num at hc <;> grind
