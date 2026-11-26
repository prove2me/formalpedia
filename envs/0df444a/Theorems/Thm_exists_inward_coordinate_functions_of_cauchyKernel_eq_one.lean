-- Prove2me | Theorems.Thm_exists_inward_coordinate_functions_of_cauchyKernel_eq_one
-- name    : exists_inward_coordinate_functions_of_cauchyKernel_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:44:51.679722+00:00
-- url     : https://prove2.me/theorems/1ae54fab-205b-564b-ae00-3076c5447c09
-- title:
--   exists inward coordinate functions of cauchy Kernel eq one: exists inward coordinate functions of cauchy Kernel eq one
-- statement:
--   Winding normalization alone supplies a global inward-coordinate choice
--   with the correct limiting parameters at every frontier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1530-L1546
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1530-L1546

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_inward_coordinate_functions_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ w ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega w = 1)
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
