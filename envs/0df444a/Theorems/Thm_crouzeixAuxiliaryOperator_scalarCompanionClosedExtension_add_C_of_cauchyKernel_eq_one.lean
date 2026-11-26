-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:00.730377+00:00
-- url     : https://prove2.me/theorems/c37309c2-1acd-4877-82dc-e367a1c7448e
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension add C of cauchy Kernel eq one: crouzeix Auxiliary Operator scalar Companion Closed Extension add C of cauchy Kernel eq one
-- statement:
--   Adding a constant polynomial shifts the canonical companion contour by
--   exactly the constant-polynomial auxiliary operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L185-L235
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L185-L235

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

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a)) =
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) +
        crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by sorry
