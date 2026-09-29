-- Prove2me | solution 2 for flt5_zw5_pid_ring_extract
-- status  : ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:38:52.713497+00:00
-- url     : https://prove2.me/submissions/5561a51e-9aea-43ae-a7bb-01d90110f1ad

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_zz5_beta_norm_exists
import Theorems.Thm_flt5_zz5_fifth_root_norm

-- Sketch for flt5_zw5_pid_ring_extract
-- Given: gcd(a,b)=1, Phi(a,b)=5*s^5, 5|(a+b), IsPID(ZZ5)
-- Strategy:
--   Child 1 (flt5_zz5_beta_norm_exists): define β₁=(a+ζb)/λ in ZZ5,
--     using 5|(a+b) to show λ|(a+ζb). Compute N(β₁)=s^5.
--   Child 2 (flt5_zz5_fifth_root_norm): from β₁ with N(β₁)=s^5 and gcd(a,b)=1
--     (coprimeness of β₁ with its conjugates) + PID, extract d with d^5~β₁.
--     Then N(d)^5 = N(β₁) = s^5.

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (h5sum : (5 : ℤ) ∣ a + b)
    (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) :
    ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  obtain ⟨β, hβ⟩ := flt5_zz5_beta_norm_exists a b s h_cop hPhi h5sum hPID
  exact flt5_zz5_fifth_root_norm a b s h_cop β hβ hPID
