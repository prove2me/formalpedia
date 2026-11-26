-- Prove2me | Theorems.Thm_exists_inward_coordinates_of_cauchyKernel_eq_one
-- name    : exists_inward_coordinates_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:44.316075+00:00
-- url     : https://prove2.me/theorems/ad89b37c-08f4-5842-acf4-d1324160ea49
-- title:
--   exists inward coordinates of cauchy Kernel eq one: exists inward coordinates of cauchy Kernel eq one
-- statement:
--   Under winding normalization, every carrier point has inward coordinates
--   without a separate boundedness hypothesis.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L300-L308
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L300-L308

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_inward_coordinates_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ w ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega w = 1)
    {c z : ℂ} (hc : c ∈ Omega.carrier) (hz : z ∈ Omega.carrier) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ eta ∈ frontier Omega.carrier,
      smoothJordanInwardPoint c eta r = z := by sorry
