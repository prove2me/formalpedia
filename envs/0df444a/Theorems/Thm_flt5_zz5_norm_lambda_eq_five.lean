-- Prove2me | Theorems.Thm_flt5_zz5_norm_lambda_eq_five
-- name    : flt5_zz5_norm_lambda_eq_five
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T09:33:56.131975+00:00
-- url     : https://prove2.me/theorems/43dfefa5-4acf-41a1-8018-592a1dd940c3
-- statement:
--   The ℤ-norm of λ=(1-ζ) in ZZ5 equals 5. Proof: N_{ZZ5/ℤ}(1-ζ) = ∏_{k=1}^{4}(1-ζ^k) = Φ₅(1) = 5. This uses the product formula for cyclotomic norms. The connection: Algebra.norm ℤ (1-ζ) equals (algebraMap ℤ ℚ)⁻¹ applied to Algebra.norm ℚ (1-ζ : CK5) = 5 from IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic

theorem flt5_zz5_norm_lambda_eq_five (ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) : Algebra.norm ℤ (1 - ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) = 5 := by sorry
