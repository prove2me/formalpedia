-- Prove2me | Theorems.Thm_flt5_zeta5_ring_witnesses
-- name    : flt5_zeta5_ring_witnesses
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T15:45:27.712635+00:00
-- url     : https://prove2.me/theorems/28b11531-b4e1-4e7a-819e-af02a35cf567

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_zeta5_ring_witnesses (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by sorry
