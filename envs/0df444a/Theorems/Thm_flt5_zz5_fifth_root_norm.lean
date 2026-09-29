-- Prove2me | Theorems.Thm_flt5_zz5_fifth_root_norm
-- name    : flt5_zz5_fifth_root_norm
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-13T08:17:44.589674+00:00
-- url     : https://prove2.me/theorems/eafb1e44-10f7-4d8b-8f80-f4c085354e38

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_zz5_fifth_root_norm (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by sorry
