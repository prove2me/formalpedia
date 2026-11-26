-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:17.725801+00:00
-- url     : https://prove2.me/theorems/5216d11f-adc5-5c69-a37d-0dedfb738db0
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension of nested: crouzeix Auxiliary Operator scalar Companion Closed Extension of nested
-- statement:
--   If one smooth Jordan domain compactly contains another, applying the
--   inner auxiliary calculus to the outer scalar companion reproduces the outer
--   conjugate-polynomial auxiliary contour.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L431-L478
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L431-L478

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hnest : closure Omega.carrier ⊆ Psi.carrier) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Psi p) =
      crouzeixPolynomialAuxiliaryOperator A Psi p := by sorry
