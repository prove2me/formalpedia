-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:10.417472+00:00
-- url     : https://prove2.me/theorems/d7ef35db-c3fe-460c-9d03-4ce45ad6166c
-- title:
--   norm crouzeix Polynomial Scalar Companion le of boundary tendsto: norm crouzeix Polynomial Scalar Companion le of boundary tendsto
-- statement:
--   Pointwise Plemelj limits with frontier norm at most `C` imply the sharp
--   interior companion bound.  The continuous closed-domain extension is
--   constructed canonically, so no separate extension function or compatibility
--   proof is required.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L137-L155
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L137-L155

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z)))
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖b z‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by sorry
