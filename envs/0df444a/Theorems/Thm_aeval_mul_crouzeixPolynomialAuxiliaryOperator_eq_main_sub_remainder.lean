-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:37.181258+00:00
-- url     : https://prove2.me/theorems/5e6e0897-96fe-5d1c-a162-8a2e9d03f38e
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator eq main sub remainder: aeval mul crouzeix Polynomial Auxiliary Operator eq main sub remainder
-- statement:
--   The product `p(A) G` is the normalized scalar-square resolvent contour
--   minus the normalized polynomial divided-difference remainder contour.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L495-L513
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L495-L513

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => star (Polynomial.eval z p) •
              Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
            Omega.boundaryParam := by sorry
