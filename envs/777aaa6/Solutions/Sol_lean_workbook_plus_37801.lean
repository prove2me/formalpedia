-- Prove2me | solution 1 for lean_workbook_plus_37801
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:43:43.78197+00:00
-- url     : https://prove2.me/submissions/f49d1546-82de-4f88-a310-03bb028f9e25

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 → n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
  intro h
  have key : n ^ 2 % 3 = (n % 3) * (n % 3) % 3 := by
    rw [pow_two, Int.mul_emod]
  rcases h with h | h | h <;> rw [key, h] <;> norm_num
