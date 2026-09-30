-- Prove2me | solution 1 for lean_workbook_plus_58747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:07:42.716108+00:00
-- url     : https://prove2.me/submissions/5ff4ce1b-be76-4cd6-949c-a7a0a3b2f59e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℝ) (a1 : a 0 = 4) (a2 : a 1 = 7)
    (a_rec : ∀ n, n ≥ 2 → a (n + 1) = 2 * a n - a (n - 1) + 2) :
    ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  let P (n : ℕ) : ℝ := (n : ℝ) ^ 2 + (a 2 - 10) * n + 16 - a 2
  have hclosed (k : ℕ) : a (k + 1) = P (k + 1) := by
    induction k using Nat.twoStepInduction with
    | zero =>
        rw [a2]
        dsimp [P]
        ring
    | one =>
        dsimp [P]
        norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
        ring
    | more k ih0 ih1 =>
        have ha := a_rec (k + 2) (by omega)
        rw [show k + 2 - 1 = k + 1 by omega, ih0, ih1] at ha
        rw [ha]
        dsimp [P]
        push_cast
        ring
  refine ⟨fun n => if n = 0 then 4 else P n, ?_⟩
  intro n
  cases n with
  | zero => simpa using a1
  | succ n => simpa using hclosed n

#print axioms solution
