-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:05.787404+00:00
-- url     : https://prove2.me/theorems/81647ab7-3efd-5367-88fe-9f321c600e2c
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator le main add remainder: norm aeval mul crouzeix Polynomial Auxiliary Operator le main add remainder
-- statement:
--   The triangle-inequality consequence of the exact separated contour
--   identity.  This estimate is valid, but it does not retain the cancellation
--   needed for the sharp `m²` product bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L570-L586
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L570-L586

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
            resolvent A z) Omega.boundaryParam‖ +
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam‖ := by sorry
