-- Prove2me | Theorems.Thm_diffContOnCl_crouzeixPolynomialScalarCompanion_extension
-- name    : diffContOnCl_crouzeixPolynomialScalarCompanion_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:07.892908+00:00
-- url     : https://prove2.me/theorems/c26a45d6-4b62-57a5-bfde-164fd202fbc1
-- title:
--   diff Cont On Cl crouzeix Polynomial Scalar Companion extension: diff Cont On Cl crouzeix Polynomial Scalar Companion extension
-- statement:
--   A function continuous on the closed smooth Jordan domain and equal to the
--   scalar companion in the interior is complex differentiable in the interior.
--   Thus it has the exact regularity required by the maximum-modulus principle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L86-L99
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L86-L99

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem diffContOnCl_crouzeixPolynomialScalarCompanion_extension
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier) :
    DiffContOnCl ℂ g Omega.carrier := by sorry
