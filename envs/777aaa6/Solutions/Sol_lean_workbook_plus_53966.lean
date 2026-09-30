-- Prove2me | solution 1 for lean_workbook_plus_53966
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:17.667551+00:00
-- url     : https://prove2.me/submissions/ef8d9ac0-bc52-4ad1-92ee-245a0a84551c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem root_power_recurrence (c r : ℝ) (hr : r ^ 2 = c * r + 1) (n : ℕ) :
    r ^ (n + 2) = c * r ^ (n + 1) + r ^ n := by
  rw [pow_add, hr, pow_succ]
  ring

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 3)
    (a_rec : ∀ n, a (n + 2) = 2 * a (n + 1) + a n) :
    ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : (1 + Real.sqrt 2) ^ 2 = 2 * (1 + Real.sqrt 2) + 1 := by nlinarith
  have hm : (1 - Real.sqrt 2) ^ 2 = 2 * (1 - Real.sqrt 2) + 1 := by nlinarith
  refine ⟨fun n => ((1 + Real.sqrt 2) ^ (n + 1) + (1 - Real.sqrt 2) ^ (n + 1)) / 2, ?_⟩
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [a0]
      norm_num only [Nat.reduceAdd, pow_one]
      ring
  | one =>
      rw [a1]
      norm_num only [Nat.reduceAdd]
      nlinarith
  | more n ih0 ih1 =>
      rw [a_rec, ih0, ih1]
      dsimp only
      rw [show n + 2 + 1 = (n + 1) + 2 by omega]
      rw [root_power_recurrence 2 _ hp (n + 1), root_power_recurrence 2 _ hm (n + 1)]
      ring

#print axioms solution
