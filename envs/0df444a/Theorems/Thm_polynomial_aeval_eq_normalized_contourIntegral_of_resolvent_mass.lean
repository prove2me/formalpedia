-- Prove2me | Theorems.Thm_polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
-- name    : polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:36.510899+00:00
-- url     : https://prove2.me/theorems/9b405a35-bef0-5d87-9ba9-35572907c98b
-- title:
--   polynomial aeval eq normalized contour Integral of resolvent mass: polynomial aeval eq normalized contour Integral of resolvent mass
-- statement:
--   A single resolvent-mass identity implies the normalized operator Cauchy
--   formula for every polynomial.  No general-domain Cauchy theorem is needed for
--   the polynomial remainder: it vanishes by an explicit primitive computation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyFromResolventMass.lean#L144-L211
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyFromResolventMass.lean#L144-L211

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (p : Polynomial ℂ) :
    Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam := by sorry
