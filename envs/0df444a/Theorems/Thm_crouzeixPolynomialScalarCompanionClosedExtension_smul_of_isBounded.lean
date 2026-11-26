-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:50.196558+00:00
-- url     : https://prove2.me/theorems/8e5e095c-7b0e-4d2c-a04b-f77b642b21b2
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension smul of is Bounded: crouzeix Polynomial Scalar Companion Closed Extension smul of is Bounded
-- statement:
--   On a bounded normalized smooth Jordan carrier, the canonical closed
--   scalar companion is conjugate-homogeneous throughout the closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1733-L1749
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1733-L1749

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by sorry
