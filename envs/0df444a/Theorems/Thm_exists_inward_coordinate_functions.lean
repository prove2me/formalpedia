-- Prove2me | Theorems.Thm_exists_inward_coordinate_functions
-- name    : exists_inward_coordinate_functions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:29.395142+00:00
-- url     : https://prove2.me/theorems/f0c63917-0182-58b2-a24f-649857dc40ba
-- title:
--   exists inward coordinate functions: exists inward coordinate functions
-- statement:
--   Inward coordinates may be chosen simultaneously for all carrier points.
--   For every frontier point, the chosen radius and endpoint tend to zero and
--   that frontier point respectively.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1435-L1526
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1435-L1526

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_inward_coordinate_functions
    (Omega : SmoothJordanDomain)
    (hbounded : Bornology.IsBounded Omega.carrier)
    {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ radius : ℂ → ℝ, ∃ endpoint : ℂ → ℂ,
      (∀ z ∈ Omega.carrier,
        radius z ∈ Ioc (0 : ℝ) 1 ∧
        endpoint z ∈ frontier Omega.carrier ∧
        smoothJordanInwardPoint c (endpoint z) (radius z) = z) ∧
      ∀ xi ∈ frontier Omega.carrier,
        Filter.Tendsto (fun z => (radius z, endpoint z))
          (nhdsWithin xi Omega.carrier)
          (nhdsWithin (0, xi)
            (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)) := by sorry
