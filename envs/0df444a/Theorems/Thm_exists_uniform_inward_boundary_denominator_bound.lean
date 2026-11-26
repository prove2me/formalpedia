-- Prove2me | Theorems.Thm_exists_uniform_inward_boundary_denominator_bound
-- name    : exists_uniform_inward_boundary_denominator_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:49.723355+00:00
-- url     : https://prove2.me/theorems/cea18211-005c-49db-bc77-4c14f2addc34
-- title:
--   exists uniform inward boundary denominator bound: exists uniform inward boundary denominator bound
-- statement:
--   One ball about an interior center gives the same linear-in-`r`
--   separation estimate simultaneously for every chord endpoint and every test
--   point on the frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L313-L355
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L313-L355

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_uniform_inward_boundary_denominator_bound
    (Omega : SmoothJordanDomain) {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
          r * delta ≤ ‖sigma - smoothJordanInwardPoint c xi r‖ := by sorry
