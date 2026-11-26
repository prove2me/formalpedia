-- Prove2me | Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
-- name    : crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:35.331179+00:00
-- url     : https://prove2.me/theorems/6329894e-d645-404e-a5b4-ff696750c3dd
-- title:
--   crouzeix Boundary Double Layer Density ball eq inv two pi of ne: crouzeix Boundary Double Layer Density ball eq inv two pi of ne
-- statement:
--   Away from its boundary base point, the double-layer density of a
--   positive circle is the constant `1 / (2 pi)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L47-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L47-L79

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) (t : ℝ)
    (hne : circleMap c R t ≠ xi) :
    crouzeixBoundaryDoubleLayerDensity
        (SmoothJordanDomain.ball c R hR) xi t = (2 * Real.pi)⁻¹ := by sorry
