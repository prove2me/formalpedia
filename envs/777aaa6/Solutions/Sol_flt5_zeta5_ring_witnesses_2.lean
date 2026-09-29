-- Prove2me | solution 2 for flt5_zeta5_ring_witnesses
-- status  : ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T06:27:09.416866+00:00
-- url     : https://prove2.me/submissions/f5c4e83a-cc7e-47e9-b20d-125a1d91749a

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_cyc5_pid_descent_core

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  haveI h_cyc : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  haveI h_nf : NumberField (CyclotomicField 5 ℚ) :=
    IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)
  have hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) :=
    IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
  exact flt5_cyc5_pid_descent_core a b c r s c1
    h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs hPID
