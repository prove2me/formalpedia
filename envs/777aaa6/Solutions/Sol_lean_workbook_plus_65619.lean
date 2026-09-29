-- Prove2me | solution 1 for lean_workbook_plus_65619
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:32.156262+00:00
-- url     : https://prove2.me/submissions/7118ebf7-f5e6-4fc2-aeff-bc8664fb9947

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
theorem solution : ¬ (∀ (a : ℝ) (h : a^2 + 3*a - 2 = 0), a = -2 ∨ a = 1) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  let a : ℝ := (-3 + Real.sqrt 17) / 2
  have he : a^2 + 3*a - 2 = 0 := by dsimp [a]; nlinarith only [hs]
  intro h
  rcases h a he with hp | hp <;> rw [hp] at he <;> norm_num at he
