-- Prove2me | Theorems.Thm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
-- name    : aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:03.91522+00:00
-- url     : https://prove2.me/theorems/6787477a-0567-542e-ba17-c96a6abf0a4b
-- title:
--   aeval add star crouzeix Polynomial Auxiliary Operator eq double Layer Integral of cauchy: aeval add star crouzeix Polynomial Auxiliary Operator eq double Layer Integral of cauchy
-- statement:
--   Assuming the normalized contour Cauchy representation of `p(A)`, the
--   symmetrized operator `p(A) + G†` is `(2π)⁻¹` times the integral of the
--   boundary values of `p` against the double-layer resolvent kernel.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SymmetrizedAuxiliary.lean#L30-L132
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SymmetrizedAuxiliary.lean#L30-L132

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam) :
    Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p) =
      (2 * Real.pi)⁻¹ •
        (∫ t in (0 : ℝ)..(2 * Real.pi),
          Polynomial.eval (Omega.boundaryParam t) p •
            (((-I * deriv Omega.boundaryParam t) •
                resolvent A (Omega.boundaryParam t)) +
              ContinuousLinearMap.adjoint
                ((-I * deriv Omega.boundaryParam t) •
                  resolvent A (Omega.boundaryParam t)))) := by sorry
