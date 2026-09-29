-- Prove2me | solution 1 for flt5_kummer_arith_descent
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T09:55:46.619099+00:00
-- url     : https://prove2.me/submissions/a231199b-076c-431b-8566-86fa199eaae4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_arith_descent
import Theorems.Thm_flt5_descent_arith_core_v2

-- Sketch: flt5_kummer_arith_descent
-- The parameter nd:ℤ with nd^5=s^5 is a norm witness from ZZ5 descent.
-- By injectivity of x^5 on ℤ, nd=s, so nd is redundant.
-- Delegate to flt5_descent_arith_core_v2 which proves the descent without nd.

theorem solution (a b c r s c1 nd : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1)
    (hnd : nd ^ 5 = s ^ 5) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  -- nd and hnd are irrelevant: the descent arithmetic depends only on a,b,c,r,s,c1
  exact flt5_descent_arith_core_v2 a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs
