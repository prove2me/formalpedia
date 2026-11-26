-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:13:43.339724+00:00
-- url     : https://prove2.me/theorems/98d25b5f-82a7-4b2c-9a4f-ced95be5b7e4
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension affine of cauchy Kernel eq one: crouzeix Auxiliary Operator scalar Companion Closed Extension affine of cauchy Kernel eq one
-- statement:
--   The auxiliary contour of the canonical companion satisfies the full
--   conjugate-affine law.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L270-L287
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L270-L287

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

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (a b : ℂ) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (a • p + Polynomial.C b)) =
      star a • crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) +
        crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C b) := by sorry
