-- Prove2me | Theorems.Thm_exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
-- name    : exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:27.581571+00:00
-- url     : https://prove2.me/theorems/db880155-f5a6-59ea-8e07-b8a93d00ffa7
-- title:
--   exists uniform norm inward regularized integrand sub le deriv: exists uniform norm inward regularized integrand sub le deriv
-- statement:
--   Joint continuity of the divided difference and the uniform chord
--   geometry give a single integrable majorant, depending only on the fixed
--   center and polynomial, for all frontier endpoints and inward radii.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L542-L582
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L542-L582

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
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
            C * ‖deriv Omega.boundaryParam t‖ := by sorry
