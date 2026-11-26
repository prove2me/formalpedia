-- Prove2me | Theorems.Thm_norm_contourIntegral_le_of_norm_le_const
-- name    : norm_contourIntegral_le_of_norm_le_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:32.817921+00:00
-- url     : https://prove2.me/theorems/030069c5-0654-447d-a4ca-14256cd1be39
-- title:
--   norm contour Integral le of norm le const: norm contour Integral le of norm le const
-- statement:
--   The length-type bound: if the integrand `γ'(t) • f (γ t)` is bounded by `C` on
--   `[0, 2π]`, the contour integral is bounded by `2π C`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L127-L138
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L127-L138

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_contourIntegral_le_of_norm_le_const {f : ℂ → F} {γ : ℝ → ℂ} {C : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) (2 * π), ‖deriv γ t • f (γ t)‖ ≤ C) :
    ‖contourIntegral f γ‖ ≤ 2 * π * C := by sorry
