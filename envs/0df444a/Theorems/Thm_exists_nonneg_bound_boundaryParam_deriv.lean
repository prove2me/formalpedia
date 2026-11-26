-- Prove2me | Theorems.Thm_exists_nonneg_bound_boundaryParam_deriv
-- name    : exists_nonneg_bound_boundaryParam_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:04.126491+00:00
-- url     : https://prove2.me/theorems/d6da25b1-b30c-490c-b196-b4bca0ffa5fa
-- title:
--   exists nonneg bound boundary Param deriv: exists nonneg bound boundary Param deriv
-- statement:
--   The speed of a smooth Jordan parametrization is uniformly bounded on the
--   compact parameter interval.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L36-L56
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L36-L56

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem exists_nonneg_bound_boundaryParam_deriv
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D := by sorry
