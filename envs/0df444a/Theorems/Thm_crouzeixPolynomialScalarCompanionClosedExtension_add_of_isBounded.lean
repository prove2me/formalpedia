-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:07:36.302086+00:00
-- url     : https://prove2.me/theorems/dc30af6f-8976-4e52-a446-f61f8eb6bd7b
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension add of is Bounded: crouzeix Polynomial Scalar Companion Closed Extension add of is Bounded
-- statement:
--   On a bounded normalized smooth Jordan carrier, the canonical closed
--   scalar companion preserves polynomial addition throughout the closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1708-L1729
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1708-L1729

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by sorry
