-- Prove2me | solution 3 for flt5_cyclotomic_pid_descent_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T09:01:18.598975+00:00
-- url     : https://prove2.me/submissions/6063e0b6-06b4-411d-980c-bd829f600fc2

import Mathlib
import Theorems.Thm_flt5_cyc5_pid_descent_core


theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q :=
  flt5_cyc5_pid_descent_core a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs hPID
