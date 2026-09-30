-- Prove2me | solution 1 for lean_workbook_plus_69250
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:26:50.341507+00:00
-- url     : https://prove2.me/submissions/a06f8e85-4edb-4f30-9940-29308458addc

import Mathlib

theorem second_order_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    1 + (n : ℝ)*x + (n.choose 2 : ℝ)*x^2 ≤ (1+x)^n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Nat.choose_zero_succ, zero_mul, add_zero, pow_zero, le_refl]
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+x by linarith)
    have hr : 0 ≤ (n.choose 2 : ℝ)*x^3 := by positivity
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_succ,
      pow_succ]
    nlinarith only [hm, hr]

theorem solution : (3001 : ℝ)/1000 < (1+4/6003)^2001 := by
  calc
    (3001 : ℝ)/1000 <
        1 + (2001 : ℝ)*(4/6003) + ((2001 : ℕ).choose 2 : ℝ)*(4/6003)^2 := by
      norm_num [Nat.choose_two_right]
    _ ≤ (1+4/6003)^2001 := second_order_bound (4/6003) (by positivity) 2001
