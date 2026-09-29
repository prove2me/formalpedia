-- Prove2me | Theorems.Thm_flt5_zz5_lambda_dvd_five
-- name    : flt5_zz5_lambda_dvd_five
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T09:33:25.019019+00:00
-- url     : https://prove2.me/theorems/0859ae80-108f-437c-a90d-1b318f83dbe6
-- statement:
--   In ZZ5 = Z[ζ₅], the element λ=(1-ζ) divides 5. This follows from the product formula: (1-ζ)(1-ζ²)(1-ζ³)(1-ζ⁴) = Φ₅(1) = 5 in Z[ζ₅]. Since this product equals 5, each factor (including 1-ζ) divides 5. Key: ζ is passed as parameter with IsPrimitiveRoot hypothesis to avoid instance issues.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Data.Int.Basic

theorem flt5_zz5_lambda_dvd_five (ζ : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) : (1 - ζ) ∣ (5 : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) := by sorry
