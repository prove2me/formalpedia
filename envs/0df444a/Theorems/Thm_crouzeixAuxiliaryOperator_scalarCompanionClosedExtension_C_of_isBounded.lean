-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:17.111583+00:00
-- url     : https://prove2.me/theorems/f88d177d-5146-5759-940f-723674a3c96b
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension C of is Bounded: crouzeix Auxiliary Operator scalar Companion Closed Extension C of is Bounded
-- statement:
--   For a constant polynomial, the canonical closed companion has exactly
--   the conjugate-polynomial auxiliary contour; no extra Plemelj identity is
--   needed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2086-L2115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2086-L2115

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a)) =
      crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by sorry
