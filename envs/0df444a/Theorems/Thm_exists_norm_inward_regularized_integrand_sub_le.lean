-- Prove2me | Theorems.Thm_exists_norm_inward_regularized_integrand_sub_le
-- name    : exists_norm_inward_regularized_integrand_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:33.106556+00:00
-- url     : https://prove2.me/theorems/88869f70-d265-5470-a81f-fe67a3091468
-- title:
--   exists norm inward regularized integrand sub le: exists norm inward regularized integrand sub le
-- statement:
--   Along inward chords, the parameterized regularized kernel minus its
--   self-kernel is uniformly dominated by a constant times the continuous
--   integrable function `‖boundaryParam'‖ * ‖q.eval boundaryParam‖`, where
--   `q = p /ₘ (X - C xi)`.  This is the exact domination input for a radial
--   Plemelj limit.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L589-L687
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L589-L687

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_norm_inward_regularized_integrand_sub_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖deriv Omega.boundaryParam t •
          (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t -
                smoothJordanInwardPoint c xi r)⁻¹) -
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t - xi)⁻¹))‖ ≤
          C * (‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval (Omega.boundaryParam t)
              (p /ₘ (Polynomial.X - Polynomial.C xi))‖) := by sorry
