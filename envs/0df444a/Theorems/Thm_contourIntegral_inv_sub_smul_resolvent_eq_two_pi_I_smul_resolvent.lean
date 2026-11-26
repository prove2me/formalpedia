-- Prove2me | Theorems.Thm_contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
-- name    : contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:27.716461+00:00
-- url     : https://prove2.me/theorems/7d070d8c-fc13-5b3d-97bc-082ae685ce4c
-- title:
--   contour Integral inv sub smul resolvent eq two pi I smul resolvent: contour Integral inv sub smul resolvent eq two pi I smul resolvent
-- statement:
--   Integrating the nested exterior Cauchy kernel against a resolvent contour
--   returns the resolvent at the exterior point, with the unnormalized contour
--   mass factor.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L77-L186
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L77-L186

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (sigma : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsigma : sigma ∉ closure Omega.carrier) :
    contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • resolvent A sigma := by sorry
