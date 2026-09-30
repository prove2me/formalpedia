-- Prove2me | solution 1 for lean_workbook_plus_81137
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:23.741596+00:00
-- url     : https://prove2.me/submissions/6401fd33-0d53-4289-869f-aaafe01592e2

import Mathlib

theorem solution (m : ℕ) :
    (5^(2*m+3) = (3*5^m)^2 + (4*5^m)^2 + (10*5^m)^2) ∧
    (5^(2*m+4) = (12*5^m)^2 + (15*5^m)^2 + (16*5^m)^2) := by
  rw [show 2*m+3 = m*2+3 by omega, show 2*m+4 = m*2+4 by omega]
  constructor <;> norm_num [pow_add, pow_mul, mul_pow] <;> ring
