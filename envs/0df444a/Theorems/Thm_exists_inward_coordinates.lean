-- Prove2me | Theorems.Thm_exists_inward_coordinates
-- name    : exists_inward_coordinates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:07:05.584198+00:00
-- url     : https://prove2.me/theorems/a0898c83-05aa-56c8-81d4-73cc2655c5c0
-- title:
--   exists inward coordinates: exists inward coordinates
-- statement:
--   In a bounded smooth Jordan carrier, every interior point is an inward
--   chord point from any fixed interior center to some frontier endpoint.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L206-L296
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L206-L296

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_inward_coordinates
    (Omega : SmoothJordanDomain)
    (hbounded : Bornology.IsBounded Omega.carrier)
    {c z : ℂ} (hc : c ∈ Omega.carrier) (hz : z ∈ Omega.carrier) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ eta ∈ frontier Omega.carrier,
      smoothJordanInwardPoint c eta r = z := by sorry
