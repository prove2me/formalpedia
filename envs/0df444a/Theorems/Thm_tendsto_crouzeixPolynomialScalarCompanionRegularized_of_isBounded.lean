-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:29.654814+00:00
-- url     : https://prove2.me/theorems/ae5d3180-a971-4fcf-8f38-733328a0c78b
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized of is Bounded: tendsto crouzeix Polynomial Scalar Companion Regularized of is Bounded
-- statement:
--   On every bounded smooth Jordan carrier, the regularized scalar companion
--   has the full unrestricted interior Plemelj limit at each frontier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1550-L1576
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1550-L1576

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by sorry
