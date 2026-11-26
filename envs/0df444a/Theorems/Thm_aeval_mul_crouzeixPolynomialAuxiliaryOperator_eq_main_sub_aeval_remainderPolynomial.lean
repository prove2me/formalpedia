-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:29.689654+00:00
-- url     : https://prove2.me/theorems/762a1ffa-e251-4851-8bcc-5060c5ac397b
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator eq main sub aeval remainder Polynomial: aeval mul crouzeix Polynomial Auxiliary Operator eq main sub aeval remainder Polynomial
-- statement:
--   The product `p(A) G` is the scalar-square resolvent contour minus
--   functional calculus of the explicitly constructed lower-degree remainder
--   polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L518-L531
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L518-L531

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by sorry
