-- Prove2me | Theorems.Thm_coefficients_scaled_product_degree_boundary
-- name    : coefficients_scaled_product_degree_boundary
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:34:47.25599+00:00
-- url     : https://prove2.me/theorems/f4650f54-b076-4771-a6df-299e76c45da1
-- title:
--   Boundary coefficients of a product with identity linear terms
-- statement:
--   At the total exponent degree, the unscaled product has coefficient one at the exponent vector and zero at every other exponent vector.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem coefficients_scaled_product_degree_boundary
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    (∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (m.prod (fun i k => phi i ^ k)) =
          (if m = Finsupp.equivFunOnFinite.symm e then 1 else 0) := by sorry
