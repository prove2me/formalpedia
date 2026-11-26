-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:15.95017+00:00
-- url     : https://prove2.me/theorems/02bcaf97-dada-57e1-8f27-bda1f8f5c71e
-- title:
--   norm crouzeix Polynomial Scalar Companion le of boundary extension: norm crouzeix Polynomial Scalar Companion le of boundary extension
-- statement:
--   A continuous boundary extension with norm at most `C` on the frontier
--   gives the same sharp bound for the actual scalar companion at every interior
--   point.  Consequently, the remaining contraction input is precisely the
--   Plemelj extension and its boundary estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L120-L131
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L120-L131

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier)
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖g z‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by sorry
