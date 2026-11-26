-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:28.229297+00:00
-- url     : https://prove2.me/theorems/2a3722b5-b888-41d6-bc48-a38bf3414655
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized inward sub self joint: tendsto crouzeix Polynomial Scalar Companion Regularized inward sub self joint
-- statement:
--   The radial Plemelj error tends to zero jointly when the inward radius
--   tends to zero and the chord endpoint varies along the frontier.  The target
--   self-value moves with the endpoint; continuity of that self-value is a
--   separate remaining step.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L943-L1140
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L943-L1140

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2
            (smoothJordanInwardPoint c x.2 x.1) -
          crouzeixPolynomialScalarCompanionRegularized Omega p x.2 x.2)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds 0) := by sorry
