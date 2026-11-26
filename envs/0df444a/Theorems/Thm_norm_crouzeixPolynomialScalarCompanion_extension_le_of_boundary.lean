-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
-- name    : norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:06.935061+00:00
-- url     : https://prove2.me/theorems/f99ca941-97b7-56e5-8b20-bc31498b9e50
-- title:
--   norm crouzeix Polynomial Scalar Companion extension le of boundary: norm crouzeix Polynomial Scalar Companion extension le of boundary
-- statement:
--   On a bounded smooth Jordan domain, a frontier norm bound for a continuous
--   extension of the scalar companion propagates to the entire closed domain.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L103-L114
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L103-L114

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier)
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖g z‖ ≤ C)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖g z‖ ≤ C := by sorry
