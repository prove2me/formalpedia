-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:03.730662+00:00
-- url     : https://prove2.me/theorems/c68af891-ef7f-5337-a1d3-9cea2d334f01
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension C of cauchy Kernel eq one: crouzeix Auxiliary Operator scalar Companion Closed Extension C of cauchy Kernel eq one
-- statement:
--   Consequently, the auxiliary contour of a constant canonical companion is
--   automatic under winding normalization alone.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2134-L2147
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2134-L2147

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a)) =
      crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by sorry
