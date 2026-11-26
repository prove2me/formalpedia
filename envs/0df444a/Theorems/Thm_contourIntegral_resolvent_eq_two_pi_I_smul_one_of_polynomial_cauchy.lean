-- Prove2me | Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
-- name    : contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:17.554332+00:00
-- url     : https://prove2.me/theorems/5b39d6c3-7ea4-4617-a084-6cfcb3981c3b
-- title:
--   contour Integral resolvent eq two pi I smul one of polynomial cauchy: contour Integral resolvent eq two pi I smul one of polynomial cauchy
-- statement:
--   A normalized Cauchy representation valid for all polynomials implies the
--   raw resolvent contour mass identity by taking the constant polynomial `1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyMass.lean#L24-L53
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyMass.lean#L24-L53

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchyP : ∀ p : Polynomial ℂ,
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            Omega.boundaryParam) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
