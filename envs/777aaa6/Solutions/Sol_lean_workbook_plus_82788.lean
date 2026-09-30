-- Prove2me | solution 1 for lean_workbook_plus_82788
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:40.627634+00:00
-- url     : https://prove2.me/submissions/6be1e6f5-1090-48af-93ba-2ded574f937a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) + 3 * a n = n ^ 3 - 1) :
    ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  have hclosed (n : ℕ) : 128 * a n =
      287 * (-3) ^ n + 32 * (n : ℤ) ^ 3 - 24 * (n : ℤ) ^ 2 - 12 * (n : ℤ) - 31 := by
    induction n with
    | zero => norm_num [a0]
    | succ n ih =>
        push_cast
        rw [pow_succ]
        linear_combination 128 * a_rec n - 3 * ih
  refine ⟨fun n =>
    (287 * (-3) ^ n + 32 * (n : ℤ) ^ 3 - 24 * (n : ℤ) ^ 2 - 12 * (n : ℤ) - 31) / 128, ?_⟩
  intro n
  dsimp only
  rw [← hclosed n]
  omega

#print axioms solution
