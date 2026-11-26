-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
-- name    : tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:43.075284+00:00
-- url     : https://prove2.me/theorems/ccbfff6f-7811-51d4-af94-ece9b2c29c90
-- title:
--   tendsto crouzeix Polynomial Scalar Companion of inward coordinates: tendsto crouzeix Polynomial Scalar Companion of inward coordinates
-- statement:
--   Any inward-coordinate chart whose radius and endpoint tend jointly to
--   `(0, xi)` transfers the joint radial theorem to the unrestricted interior
--   filter.  This isolates the remaining geometry needed for a full Plemelj
--   theorem from the completed analytic argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1361-L1383
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1361-L1383

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
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
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by sorry
