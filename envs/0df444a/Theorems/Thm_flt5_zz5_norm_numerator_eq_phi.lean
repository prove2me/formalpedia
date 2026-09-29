-- Prove2me | Theorems.Thm_flt5_zz5_norm_numerator_eq_phi
-- name    : flt5_zz5_norm_numerator_eq_phi
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T09:34:03.620026+00:00
-- url     : https://prove2.me/theorems/38497c1c-9697-499d-9630-a19d8bdf6adf
-- statement:
--   The ℤ-norm of (a+ζb) in ZZ5 equals the cyclotomic polynomial Phi5(a,b) = a^4-a^3*b+a^2*b^2-a*b^3+b^4. Proof: N_{ZZ5/ℤ}(a+ζb) = ∏_{k=1}^{4}(a+ζ^k*b) = b^4*Φ₅(-a/b) = a^4-a^3b+a^2b^2-ab^3+b^4. This uses the norm-as-product-of-conjugates formula for cyclotomic fields.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_zz5_norm_numerator_eq_phi (a b : ℤ) (ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) : Algebra.norm ℤ ((a : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) + ζ * (b : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) = a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by sorry
