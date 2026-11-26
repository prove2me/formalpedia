-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:30.099847+00:00
-- url     : https://prove2.me/theorems/1b7cdaa5-522c-57f9-b15d-2fa61c4e7a72
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension smul eq iff: crouzeix Auxiliary Operator scalar Companion Closed Extension smul eq iff
-- statement:
--   For a nonzero scalar, companion-contour reproduction is preserved and
--   reflected by polynomial scaling.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L158-L181
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L158-L181

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

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    {a : ℂ} (ha : a ≠ 0) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
        crouzeixPolynomialAuxiliaryOperator A Omega (a • p)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by sorry
