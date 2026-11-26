-- Prove2me | Theorems.Thm_exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
-- name    : exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:07:05.06037+00:00
-- url     : https://prove2.me/theorems/531df8ae-3d19-53b3-8e1d-fea1327c3f1a
-- title:
--   exists uniform norm eval div By Monic X sub C frontier le: exists uniform norm eval div By Monic X sub C frontier le
-- statement:
--   On the compact frontier, the values of all frontier-based divided
--   differences of one polynomial admit a single nonnegative bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L134-L156
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L134-L156

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ xi ∈ frontier Omega.carrier,
      ∀ sigma ∈ frontier Omega.carrier,
        ‖Polynomial.eval sigma
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤ Q := by sorry
