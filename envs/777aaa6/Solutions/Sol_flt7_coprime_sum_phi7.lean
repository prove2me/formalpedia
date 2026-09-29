-- Prove2me | solution 1 for flt7_coprime_sum_phi7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:41:40.554689+00:00
-- url     : https://prove2.me/submissions/3ab9b2bc-ea87-4f63-943d-2c20f9ff67c4

import Theorems.Thm_flt7_coprime_sum_phi7
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h_cop : Int.gcd a b = 1) :
    (a + b) * (a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2 - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4 - a * b ^ 5 +
      b ^ 6) = c ^ 7 :=
  (by ring : (a + b) * (a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2 - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4 -
      a * b ^ 5 + b ^ 6) = a ^ 7 + b ^ 7).trans h_eq
