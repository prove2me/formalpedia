-- Prove2me | Theorems.Thm_mvPowerSeries_homogeneousComponent_pow_of_constantCoeff_zero
-- name    : mvPowerSeries_homogeneousComponent_pow_of_constantCoeff_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:48:17.314965+00:00
-- url     : https://prove2.me/theorems/ca21d83f-56a3-476a-b262-0dda149c458f
-- title:
--   Homogeneous component of a power with zero constant coefficient
-- statement:
--   For a multivariate power series with zero constant coefficient, the homogeneous component of its `n`th power in degree `n` is the `n`th power of its degree-one homogeneous component. The case `n = 0` includes the empty power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Order

open scoped BigOperators

theorem mvPowerSeries_homogeneousComponent_pow_of_constantCoeff_zero
    {σ R : Type*} [CommSemiring R]
    (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.constantCoeff f = 0)
    (n : Nat) :
    MvPowerSeries.homogeneousComponent n (f ^ n) =
      (MvPowerSeries.homogeneousComponent 1 f) ^ n := by sorry
