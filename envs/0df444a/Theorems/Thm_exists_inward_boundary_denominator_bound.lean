-- Prove2me | Theorems.Thm_exists_inward_boundary_denominator_bound
-- name    : exists_inward_boundary_denominator_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:51.879157+00:00
-- url     : https://prove2.me/theorems/4510287f-903e-525b-8f0c-e8eb887adf28
-- title:
--   exists inward boundary denominator bound: exists inward boundary denominator bound
-- statement:
--   An interior ball gives a linear-in-`r` lower bound on the distance from
--   the inward chord point to every frontier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L359-L369
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L359-L369

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_inward_boundary_denominator_bound
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
        r * delta ≤ ‖sigma - smoothJordanInwardPoint c xi r‖ := by sorry
