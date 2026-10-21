-- Prove2me | Theorems.Thm_coefficients_product_of_coordinate_variables
-- name    : coefficients_product_of_coordinate_variables
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:37:23.085217+00:00
-- url     : https://prove2.me/theorems/20a4be5a-2759-483d-9836-c3bda71e19f6
-- title:
--   Coefficient of a product of coordinate variables
-- statement:
--   The product of coordinate variables with exponents `m` has coefficient one at exponent vector `m` and zero at every other exponent vector.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem coefficients_product_of_coordinate_variables
    {n : Nat}
    (m : Fin n →₀ Nat)
    (e : Fin n → Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (m.prod (fun i k => MvPowerSeries.X i ^ k)) =
    (if m = Finsupp.equivFunOnFinite.symm e then 1 else 0) := by sorry
