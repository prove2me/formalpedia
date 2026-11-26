-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:06:52.374393+00:00
-- url     : https://prove2.me/theorems/c9eeb59f-5643-5190-abb2-20c1e3d09e60
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension C of is Bounded: crouzeix Polynomial Scalar Companion Closed Extension C of is Bounded
-- statement:
--   Constant polynomials give the conjugate constant throughout the
--   canonical closed extension of a bounded normalized carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1876-L1905
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1876-L1905

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
    (Omega : SmoothJordanDomain) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (Polynomial.C a) z = star a := by sorry
