-- Prove2me | Theorems.Thm_coefficients_scaled_product_degree_boundary_linearization
-- name    : coefficients_scaled_product_degree_boundary_linearization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:37:10.930035+00:00
-- url     : https://prove2.me/theorems/76595842-10cd-4175-b5e0-ea50503cbb42
-- title:
--   Boundary coefficient linearization for products of powers
-- statement:
--   At the common total degree, replacing each series by its identity linear part preserves the coefficient of the product of powers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem coefficients_scaled_product_degree_boundary_linearization
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D)
    (hedeg : (∑ i, e i) = D) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (m.prod (fun i k => phi i ^ k)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (m.prod (fun i k => MvPowerSeries.X i ^ k)) := by sorry
