-- Prove2me | Theorems.Thm_contourIntegral_eq_zero_of_hasDerivAt_of_closed
-- name    : contourIntegral_eq_zero_of_hasDerivAt_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:30.07434+00:00
-- url     : https://prove2.me/theorems/c0d96a13-5be1-48ea-9e1e-1be68499c634
-- title:
--   contour Integral eq zero of has Deriv At of closed: contour Integral eq zero of has Deriv At of closed
-- statement:
--   Cauchy's theorem for integrands with a global primitive: along a closed differentiable
--   curve the contour integral of `f = Fp'` vanishes.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L156-L167
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L156-L167

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) (hclosed : γ (2 * π) = γ 0) :
    contourIntegral f γ = 0 := by sorry
