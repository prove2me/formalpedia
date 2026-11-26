-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:43.140938+00:00
-- url     : https://prove2.me/theorems/febd4ab9-638b-5fba-b1cb-13d1249f68d8
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized of inward coordinates: tendsto crouzeix Polynomial Scalar Companion Regularized of inward coordinates
-- statement:
--   The same inward-coordinate hypothesis supplies exactly the regularized
--   frontier convergence consumed by the canonical Plemelj extension API.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1387-L1431
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1387-L1431

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier)
    (radius : ℂ → ℝ) (endpoint : ℂ → ℂ)
    (hcoord : ∀ᶠ z in nhdsWithin xi Omega.carrier,
      smoothJordanInwardPoint c (endpoint z) (radius z) = z)
    (hparam : Filter.Tendsto (fun z => (radius z, endpoint z))
      (nhdsWithin xi Omega.carrier)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by sorry
