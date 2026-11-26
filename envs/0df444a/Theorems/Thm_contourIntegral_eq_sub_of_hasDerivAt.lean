-- Prove2me | Theorems.Thm_contourIntegral_eq_sub_of_hasDerivAt
-- name    : contourIntegral_eq_sub_of_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:45.646277+00:00
-- url     : https://prove2.me/theorems/19984aee-0db1-44c4-97c0-3485d0d65029
-- title:
--   contour Integral eq sub of has Deriv At: contour Integral eq sub of has Deriv At
-- statement:
--   Fundamental theorem of calculus along a curve: if `Fp` is a primitive of `f` along the
--   trace of the differentiable curve `γ`, the contour integral is the boundary difference.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L142-L152
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L142-L152

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_eq_sub_of_hasDerivAt [CompleteSpace F] {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) :
    contourIntegral f γ = Fp (γ (2 * π)) - Fp (γ 0) := by sorry
