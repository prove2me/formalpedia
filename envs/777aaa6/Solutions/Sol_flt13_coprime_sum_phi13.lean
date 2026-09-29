-- Prove2me | solution 1 for flt13_coprime_sum_phi13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:53:35.476095+00:00
-- url     : https://prove2.me/submissions/19cb5471-64e7-4c01-9fe0-e556109d3255

import Theorems.Thm_flt13_coprime_sum_phi13
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 13 + b ^ 13 = c ^ 13) (h_cop : Int.gcd a b = 1) :
    (a + b) * (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 -
      a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 +
      a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) = c ^ 13 :=
  (by ring : (a + b) * (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 -
      a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 +
      a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) = a ^ 13 + b ^ 13).trans h_eq
