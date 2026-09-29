-- Prove2me | solution 5 for flt5_zeta5_ring_witnesses
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-14T17:33:20.737638+00:00
-- url     : https://prove2.me/submissions/1a40c267-b0e0-4fd7-8480-81de13da5481
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_arith_descent

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  exact flt5_kummer_arith_descent a b c r s c1 s h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs rfl
