-- Prove2me | solution 1 for lean_workbook_plus_11637
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:30.909268+00:00
-- url     : https://prove2.me/submissions/bf6aa2d1-b792-4ddc-a71a-84426f672425

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Divisibility.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : 14 ∣ 3 ^ (4 * n + 2) + 5 ^ (2 * n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h4 : 4 * (n + 1) + 2 = (4 * n + 2) + 4 := by ring
    have h2 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [h4, h2, pow_add (3 : ℕ) (4 * n + 2) 4,
      pow_add (5 : ℕ) (2 * n + 1) 2]
    norm_num only [show (3 : ℕ) ^ 4 = 81 by decide, show (5 : ℕ) ^ 2 = 25 by decide]
    have heq : 3 ^ (4 * n + 2) * 81 + 5 ^ (2 * n + 1) * 25 =
        25 * (3 ^ (4 * n + 2) + 5 ^ (2 * n + 1)) +
          14 * (4 * 3 ^ (4 * n + 2)) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right ih 25) (dvd_mul_right 14 _)

#print axioms solution
