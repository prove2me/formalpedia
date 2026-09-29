-- Prove2me | Theorems.Thm_flt5_cyc5_pid_core_int_part
-- name    : flt5_cyc5_pid_core_int_part
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T07:34:30.218177+00:00
-- url     : https://prove2.me/theorems/d50accdc-5702-4a0a-bc06-a1f357b0924f

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_cyc5_pid_core_int_part (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) (d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hd_norm : (Algebra.norm ℤ d) ^ 5 = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by sorry
