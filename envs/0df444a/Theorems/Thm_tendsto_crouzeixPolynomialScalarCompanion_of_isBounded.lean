-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
-- name    : tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:05.443834+00:00
-- url     : https://prove2.me/theorems/9028b159-2047-482b-a50f-55cb549957cd
-- title:
--   tendsto crouzeix Polynomial Scalar Companion of is Bounded: tendsto crouzeix Polynomial Scalar Companion of is Bounded
-- statement:
--   Under winding normalization, the actual scalar companion converges from
--   the whole carrier to its explicit Plemelj boundary value.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1580-L1593
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1580-L1593

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by sorry
