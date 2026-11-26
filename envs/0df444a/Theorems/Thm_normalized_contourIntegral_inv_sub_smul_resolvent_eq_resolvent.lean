-- Prove2me | Theorems.Thm_normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
-- name    : normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:36.79051+00:00
-- url     : https://prove2.me/theorems/86f13946-329e-4faa-96c7-896dbe9853cd
-- title:
--   normalized contour Integral inv sub smul resolvent eq resolvent: normalized contour Integral inv sub smul resolvent eq resolvent
-- statement:
--   Normalized operator-valued Cauchy reproduction for an exterior resolvent
--   point of a smooth convex carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L190-L205
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L190-L205

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (sigma : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsigma : sigma ∉ closure Omega.carrier) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
          Omega.boundaryParam =
      resolvent A sigma := by sorry
