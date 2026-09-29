-- Prove2me | solution 1 for flt5_zeta5_ring_witnesses
-- status  : ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T06:23:07.977615+00:00
-- url     : https://prove2.me/submissions/da08d749-1663-47a6-8d7e-25abde80200e

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_cyclotomic_pid_descent_witnesses

-- Sketch: flt5_zeta5_ring_witnesses
-- Reduces to: given Z[ζ₅] is a PID, produce the Dirichlet descent witnesses p,q.
-- The PID fact (IsCyclotomicExtension.Rat.five_pid) is proved using Mathlib's
-- Mathlib.NumberTheory.NumberField.Cyclotomic.PID module.
-- The actual algebraic descent (child flt5_cyclotomic_pid_descent_witnesses) is deferred.

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  -- Step 1: Establish that Z[ζ₅] is a PID using Mathlib's NumberField.Cyclotomic.PID
  haveI h_cyc : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  haveI h_nf : NumberField (CyclotomicField 5 ℚ) :=
    IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)
  have hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) :=
    IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
  -- Step 2: Apply the child that performs the algebraic descent given the PID property
  exact flt5_cyclotomic_pid_descent_witnesses a b c r s c1
    h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs hPID
