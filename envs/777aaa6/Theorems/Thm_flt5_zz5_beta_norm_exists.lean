-- Prove2me | Theorems.Thm_flt5_zz5_beta_norm_exists
-- name    : flt5_zz5_beta_norm_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T08:17:37.490014+00:00
-- url     : https://prove2.me/theorems/24c4b430-50a9-4322-bd8c-32ccd3ef4b8b

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_zz5_beta_norm_exists (a b s : ℤ) (h_cop : Int.gcd a b = 1) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (h5sum : (5 : ℤ) ∣ a + b) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), Algebra.norm ℤ β = s ^ 5 := by sorry
