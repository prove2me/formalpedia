-- Prove2me | Theorems.Thm_flt5_zz5_norm_lambda_cast
-- name    : flt5_zz5_norm_lambda_cast
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T10:41:58.282083+00:00
-- url     : https://prove2.me/theorems/f0c96334-00d9-4764-9d57-138bcd3bfd4e
-- statement:
--   The ℤ-norm of (1-ζ) in ZZ5, cast to ℚ, equals 5. This follows from Algebra.norm_localization relating the ℤ-norm to the ℚ-norm of (1-ζ) in the cyclotomic field, combined with IsPrimitiveRoot.norm_sub_one_of_prime_ne_two giving Algebra.norm ℚ (1-ζ) = 5.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic

theorem flt5_zz5_norm_lambda_cast (ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) : (Algebra.norm ℤ (1 - ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) : ℚ) = 5 := by sorry
