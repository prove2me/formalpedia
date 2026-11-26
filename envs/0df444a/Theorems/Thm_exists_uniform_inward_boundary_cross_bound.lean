-- Prove2me | Theorems.Thm_exists_uniform_inward_boundary_cross_bound
-- name    : exists_uniform_inward_boundary_cross_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:46.072181+00:00
-- url     : https://prove2.me/theorems/9634b404-4bf1-41d5-be18-11d9c82cb09a
-- title:
--   exists uniform inward boundary cross bound: exists uniform inward boundary cross bound
-- statement:
--   For a fixed interior center, compactness of the frontier also bounds the
--   chord lengths.  Consequently the multiplied cancellation estimate has
--   constants independent of both frontier points.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L374-L406
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L374-L406

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_uniform_inward_boundary_cross_bound
    (Omega : SmoothJordanDomain) {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ delta R : ℝ, 0 < delta ∧ 0 ≤ R ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
          delta * ‖smoothJordanInwardPoint c xi r - xi‖ ≤
            R * ‖sigma - smoothJordanInwardPoint c xi r‖ := by sorry
