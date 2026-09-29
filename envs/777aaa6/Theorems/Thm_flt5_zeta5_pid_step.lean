-- Prove2me | Theorems.Thm_flt5_zeta5_pid_step
-- name    : flt5_zeta5_pid_step
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T14:45:11.491101+00:00
-- url     : https://prove2.me/theorems/7bef5b2d-0c06-46e4-9410-eb98fb0f4e7f

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_zeta5_pid_step (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p.natAbs < c.natAbs ∧ q.natAbs < c.natAbs ∧ p ≠ 0 ∧ q ≠ 0 := by sorry
