-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_eq_iff
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:13:34.464347+00:00
-- url     : https://prove2.me/theorems/9bdf6d21-994a-58f6-b738-0a4384ecf171
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension affine eq iff: crouzeix Auxiliary Operator scalar Companion Closed Extension affine eq iff
-- statement:
--   Reproduction is invariant under the full nondegenerate affine action on
--   the source polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L291-L310
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L291-L310

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

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_eq_iff
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension
            Omega (a • p + Polynomial.C b)) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (a • p + Polynomial.C b)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by sorry
