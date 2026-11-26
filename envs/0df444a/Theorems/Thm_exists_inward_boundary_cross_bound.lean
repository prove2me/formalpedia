-- Prove2me | Theorems.Thm_exists_inward_boundary_cross_bound
-- name    : exists_inward_boundary_cross_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:56.852742+00:00
-- url     : https://prove2.me/theorems/f297eff3-dee4-564d-b881-9cdf2a163f67
-- title:
--   exists inward boundary cross bound: exists inward boundary cross bound
-- statement:
--   The preceding denominator bound in the multiplied form used after the
--   resolvent identity.  The chord displacement contributes exactly the same
--   factor `r` as the boundary separation, leaving a uniform domination
--   constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L412-L434
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L412-L434

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_inward_boundary_cross_bound
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
        delta * ‖smoothJordanInwardPoint c xi r - xi‖ ≤
          ‖c - xi‖ * ‖sigma - smoothJordanInwardPoint c xi r‖ := by sorry
