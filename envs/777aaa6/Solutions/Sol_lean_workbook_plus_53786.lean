-- Prove2me | solution 1 for lean_workbook_plus_53786
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:36.677783+00:00
-- url     : https://prove2.me/submissions/afcffbd4-2ecb-4b88-8624-51e959ee06ef

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
theorem solution : ¬ (∀ a b c : ℝ, a ≥ b ∧ b ≥ c → a^2 + b^2 + c^2 ≥ Real.sqrt 3 * (a^2 - c^2)) := by
  have hn3 := Real.sqrt_nonneg (3 : ℝ)
  have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  intro h
  have hc := h 1 0 0 (by norm_num)
  norm_num at hc
  have hc' : Real.sqrt 3 ≤ (1 : ℝ) := by grind only []
  nlinarith only [hc', hs3, hn3]
