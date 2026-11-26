-- Prove2me | Theorems.Thm_smoothJordanInwardPoint_mem_carrier
-- name    : smoothJordanInwardPoint_mem_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:06:43.848377+00:00
-- url     : https://prove2.me/theorems/9a06e1db-c4ca-4eac-8fb0-3da13bd57c7e
-- title:
--   smooth Jordan Inward Point mem carrier: smooth Jordan Inward Point mem carrier
-- statement:
--   Every strict inward convex combination of a frontier point and an
--   interior point lies in the open convex carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L190-L202
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L190-L202

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem smoothJordanInwardPoint_mem_carrier
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    smoothJordanInwardPoint c xi r ∈ Omega.carrier := by sorry
