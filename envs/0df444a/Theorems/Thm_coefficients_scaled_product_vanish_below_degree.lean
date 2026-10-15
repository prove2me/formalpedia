-- Prove2me | Theorems.Thm_coefficients_scaled_product_vanish_below_degree
-- name    : coefficients_scaled_product_vanish_below_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:34:40.808371+00:00
-- url     : https://prove2.me/theorems/cdffa4bd-7922-42f2-87f8-08489d9e343a
-- title:
--   Vanishing below the total degree of a product of substituted powers
-- statement:
--   If each substituted series has zero constant term, every coefficient of the product of powers below the total exponent degree vanishes.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem coefficients_scaled_product_vanish_below_degree
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (m : Fin n →₀ Nat)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    (∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (m.prod (fun i k => phi i ^ k)) = 0 := by sorry
