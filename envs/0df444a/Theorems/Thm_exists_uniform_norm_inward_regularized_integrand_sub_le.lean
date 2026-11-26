-- Prove2me | Theorems.Thm_exists_uniform_norm_inward_regularized_integrand_sub_le
-- name    : exists_uniform_norm_inward_regularized_integrand_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:16.725094+00:00
-- url     : https://prove2.me/theorems/f2999b1d-d145-4703-856f-8b5ea48b95cf
-- title:
--   exists uniform norm inward regularized integrand sub le: exists uniform norm inward regularized integrand sub le
-- statement:
--   For a fixed interior center and polynomial, the integrand domination
--   constant can be chosen uniformly over every frontier chord endpoint.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L438-L537
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L438-L537

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_uniform_norm_inward_regularized_integrand_sub_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c : ℂ}
    (hc : c ∈ Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xi ∈ frontier Omega.carrier,
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
