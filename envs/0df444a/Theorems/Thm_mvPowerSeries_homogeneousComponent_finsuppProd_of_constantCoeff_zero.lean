-- Prove2me | Theorems.Thm_mvPowerSeries_homogeneousComponent_finsuppProd_of_constantCoeff_zero
-- name    : mvPowerSeries_homogeneousComponent_finsuppProd_of_constantCoeff_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:45:13.311636+00:00
-- url     : https://prove2.me/theorems/830bd905-624a-4f85-a6b7-158cfa11f8b8
-- title:
--   Lowest homogeneous component of a product of powers
-- statement:
--   For series with zero constant coefficients, the homogeneous component of their product of powers at the total exponent degree equals the product of the corresponding powers of their linear homogeneous components. This includes zero exponents and the empty product.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Order

open scoped BigOperators

theorem mvPowerSeries_homogeneousComponent_finsuppProd_of_constantCoeff_zero
    {σ ι R : Type*} [CommSemiring R]
    (f : ι → MvPowerSeries σ R)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (m : ι →₀ Nat) :
    MvPowerSeries.homogeneousComponent m.degree
      (m.prod (fun i k => f i ^ k)) =
    m.prod (fun i k => (MvPowerSeries.homogeneousComponent 1 (f i)) ^ k) := by sorry
