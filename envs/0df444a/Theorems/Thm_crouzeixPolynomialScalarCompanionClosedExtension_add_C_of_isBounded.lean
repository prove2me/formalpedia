-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:47.042782+00:00
-- url     : https://prove2.me/theorems/e11258ba-7d75-4c20-8b04-51c79a4a9867
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension add C of is Bounded: crouzeix Polynomial Scalar Companion Closed Extension add C of is Bounded
-- statement:
--   Adding a constant polynomial shifts the canonical closed companion by
--   the conjugate constant throughout a bounded normalized closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1909-L1923
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1909-L1923

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (p + Polynomial.C a) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z + star a := by sorry
