-- Prove2me | solution 1 for lean_workbook_plus_731
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:50.26012+00:00
-- url     : https://prove2.me/submissions/0c0a5633-72e5-4fe8-9ee2-c23d15f13792

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
theorem solution : ¬ (∀ a b c : ℝ, (a + b) / Real.sqrt (a ^ 2 + b) + (b + c) / Real.sqrt (b + c ^ 2) ≤ Real.sqrt (2 * ((a + b) ^ 2 / (a ^ 2 + b) + (b + c) ^ 2 / (b + c ^ 2))) ∧ Real.sqrt (2 * ((a + b) ^ 2 / (a ^ 2 + b) + (b + c) ^ 2 / (b + c ^ 2))) ≤ 2) := by
  have hn8 := Real.sqrt_nonneg (8 : ℝ)
  have hs8 := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  intro h
  have hc := (h 1 1 1).2
  have hc' : Real.sqrt 8 ≤ (2 : ℝ) := by
    convert hc using 1 <;> congr 1 <;> norm_num <;> grind
  nlinarith only [hc', hs8, hn8]
