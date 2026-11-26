-- Prove2me | Theorems.Thm_ae_boundaryParam_ne_of_mem_frontier
-- name    : ae_boundaryParam_ne_of_mem_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:59.067589+00:00
-- url     : https://prove2.me/theorems/18e41f77-1de4-41d2-b53e-4035d6b68887
-- title:
--   ae boundary Param ne of mem frontier: ae boundary Param ne of mem frontier
-- statement:
--   On one fundamental integration interval, a Jordan boundary
--   parametrization takes any prescribed frontier value only on a null set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L160-L181
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L160-L181

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem ae_boundaryParam_ne_of_mem_frontier
    (Omega : SmoothJordanDomain) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier) :
    ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) → Omega.boundaryParam t ≠ xi := by sorry
