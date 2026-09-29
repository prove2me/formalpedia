-- Prove2me | solution 1 for flt11_coprime_sum_phi11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:53:35.07976+00:00
-- url     : https://prove2.me/submissions/a3ff795c-2b7b-4ec6-b4f6-50dc6ec1eb8c

import Theorems.Thm_flt11_coprime_sum_phi11
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 11 + b ^ 11 = c ^ 11) (h_cop : Int.gcd a b = 1) :
    (a + b) * (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 -
      a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) =
      c ^ 11 :=
  (by ring : (a + b) * (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 -
      a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) =
      a ^ 11 + b ^ 11).trans h_eq
