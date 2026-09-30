-- Prove2me | solution 1 for lean_workbook_plus_41069
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:06:30.635918+00:00
-- url     : https://prove2.me/submissions/1c0a4e66-2598-4889-868e-d045dedf0bac

import Mathlib

set_option autoImplicit false

theorem recurrence_formula (a : ℕ → ℚ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hrec : ∀ n, a (n + 2) = 2 * a (n + 1) + 3 * a n) :
    ∀ n, a n = ((3 : ℚ) ^ n - (-1 : ℚ) ^ n) / 4 := by
  refine Nat.twoStepInduction ?_ ?_ ?_
  · norm_num [h0]
  · norm_num [h1]
  · intro n ih ih1
    rw [hrec, ih, ih1]
    simp only [pow_add, pow_one, pow_two]
    ring

theorem solution (a : ℕ → ℚ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hrec : ∀ n, a (n + 2) = 2 * a (n + 1) + 3 * a n) : a 7 = 547 := by
  rw [recurrence_formula a h0 h1 hrec 7]
  norm_num

#print axioms solution
