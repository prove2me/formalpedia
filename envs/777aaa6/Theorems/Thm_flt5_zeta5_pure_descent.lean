-- Prove2me | Theorems.Thm_flt5_zeta5_pure_descent
-- name    : flt5_zeta5_pure_descent
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T14:51:29.812757+00:00
-- url     : https://prove2.me/theorems/caaf615e-c6ee-41b5-8036-2a7146feb4ed

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_zeta5_pure_descent (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p.natAbs ≤ c1.natAbs ∧ q.natAbs ≤ c1.natAbs ∧ p ≠ 0 ∧ q ≠ 0 := by sorry
