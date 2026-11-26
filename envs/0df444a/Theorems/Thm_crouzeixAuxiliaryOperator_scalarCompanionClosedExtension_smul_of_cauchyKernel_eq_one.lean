-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:10:09.119824+00:00
-- url     : https://prove2.me/theorems/71ceeee3-9d9b-4bc6-8ea5-05ee47c0ee3d
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension smul of cauchy Kernel eq one: crouzeix Auxiliary Operator scalar Companion Closed Extension smul of cauchy Kernel eq one
-- statement:
--   Scaling a polynomial conjugate-scales the auxiliary contour of its
--   canonical closed companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L127-L153
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L127-L153

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
omit [CompleteSpace E]

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
      star a • crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Omega p) := by sorry
