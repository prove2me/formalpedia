-- Prove2me | solution 1 for lean_workbook_plus_34888
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:34.37689+00:00
-- url     : https://prove2.me/submissions/a82629b0-6260-456e-ab31-bae5649df049

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem root_power_recurrence (c r : ℝ) (hr : r ^ 2 = c * r + 1) (n : ℕ) :
    r ^ (n + 2) = c * r ^ (n + 1) + r ^ n := by
  rw [pow_add, hr, pow_succ]
  ring

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 2)
    (a_rec : ∀ n, a (n + 2) = 4 * a (n + 1) + a n) :
    ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : (2 + Real.sqrt 5) ^ 2 = 4 * (2 + Real.sqrt 5) + 1 := by nlinarith
  have hm : (2 - Real.sqrt 5) ^ 2 = 4 * (2 - Real.sqrt 5) + 1 := by nlinarith
  refine ⟨fun n => ((2 + Real.sqrt 5) ^ n + (2 - Real.sqrt 5) ^ n) / 2, ?_⟩
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [a0]
      norm_num
  | one =>
      rw [a1]
      simp only [pow_one]
      ring
  | more n ih0 ih1 =>
      rw [a_rec, ih0, ih1]
      dsimp only
      rw [root_power_recurrence 4 _ hp n, root_power_recurrence 4 _ hm n]
      ring

#print axioms solution
