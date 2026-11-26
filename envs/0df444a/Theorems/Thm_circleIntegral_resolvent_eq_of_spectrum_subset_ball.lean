-- Prove2me | Theorems.Thm_circleIntegral_resolvent_eq_of_spectrum_subset_ball
-- name    : circleIntegral_resolvent_eq_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:28.614899+00:00
-- url     : https://prove2.me/theorems/2597483a-e793-4030-9392-7ca461823b09
-- title:
--   circle Integral resolvent eq of spectrum subset ball: circle Integral resolvent eq of spectrum subset ball
-- statement:
--   The same deformation for the bare resolvent `z ↦ R_A(z)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L83-L95
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L83-L95

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_resolvent_eq_of_spectrum_subset_ball (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    circleIntegral (resolvent A) c r = circleIntegral (resolvent A) c R := by sorry
