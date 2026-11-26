-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:33.172833+00:00
-- url     : https://prove2.me/theorems/7baf9077-af44-47a1-8d67-f36bb202bef4
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension add C eq iff: crouzeix Auxiliary Operator scalar Companion Closed Extension add C eq iff
-- statement:
--   The companion-contour reproduction identity is invariant under adding a
--   constant polynomial.  It may therefore be checked after any convenient
--   constant normalization of `p`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L240-L266
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L240-L266

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension
            Omega (p + Polynomial.C a)) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (p + Polynomial.C a)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by sorry
