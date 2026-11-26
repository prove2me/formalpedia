-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
-- name    : continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:19.531453+00:00
-- url     : https://prove2.me/theorems/6c0a79be-6ec2-4ef2-84fb-b975d7bea891
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Closed Extension of is Bounded: continuous On crouzeix Polynomial Scalar Companion Closed Extension of is Bounded
-- statement:
--   On a bounded smooth Jordan carrier, winding normalization makes the
--   canonical scalar-companion extension continuous on the closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1669-L1684
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1669-L1684

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by sorry
