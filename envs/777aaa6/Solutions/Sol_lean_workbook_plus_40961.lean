-- Prove2me | solution 1 for lean_workbook_plus_40961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:08:12.559763+00:00
-- url     : https://prove2.me/submissions/5026971c-5ad1-4fd0-a970-7919dcceacc6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem root_power_recurrence (r : ℝ) (hr : r ^ 2 = 8 * r - 1) (n : ℕ) :
    r ^ (n + 2) = 8 * r ^ (n + 1) - r ^ n := by
  rw [pow_add, hr, pow_succ]
  ring

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 5) (a1 : a 1 = 35)
    (a_rec : ∀ n, a (n + 2) = 8 * a (n + 1) - a n) :
    ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  have hs : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hp : (4 + Real.sqrt 15) ^ 2 = 8 * (4 + Real.sqrt 15) - 1 := by nlinarith
  have hm : (4 - Real.sqrt 15) ^ 2 = 8 * (4 - Real.sqrt 15) - 1 := by nlinarith
  let F (n : ℕ) : ℝ :=
    ((5 + Real.sqrt 15) * (4 + Real.sqrt 15) ^ n +
      (5 - Real.sqrt 15) * (4 - Real.sqrt 15) ^ n) / 2
  have hclosed (n : ℕ) : (a n : ℝ) = F n := by
    induction n using Nat.twoStepInduction with
    | zero =>
        rw [a0]
        dsimp [F]
        ring
    | one =>
        rw [a1]
        dsimp [F]
        norm_num only [pow_one, Int.cast_ofNat]
        nlinarith
    | more n ih0 ih1 =>
        rw [a_rec]
        push_cast
        rw [ih0, ih1]
        dsimp [F]
        rw [root_power_recurrence _ hp n, root_power_recurrence _ hm n]
        ring
  refine ⟨fun n => ⌊F n⌋, ?_⟩
  intro n
  dsimp only
  rw [← hclosed n]
  simp

#print axioms solution
