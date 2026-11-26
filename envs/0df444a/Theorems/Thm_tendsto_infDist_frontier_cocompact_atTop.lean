-- Prove2me | Theorems.Thm_tendsto_infDist_frontier_cocompact_atTop
-- name    : tendsto_infDist_frontier_cocompact_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:00.123938+00:00
-- url     : https://prove2.me/theorems/f99a2ce4-ed7d-5bc6-a7eb-a482372dbca7
-- title:
--   tendsto inf Dist frontier cocompact at Top: tendsto inf Dist frontier cocompact at Top
-- statement:
--   The distance from a point to a compact Jordan frontier tends to infinity
--   as the point tends to infinity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L192-L211
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L192-L211

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem tendsto_infDist_frontier_cocompact_atTop
    (Omega : SmoothJordanDomain) :
    Tendsto (fun z : ℂ ↦ Metric.infDist z (frontier Omega.carrier))
      (cocompact ℂ) atTop := by sorry
