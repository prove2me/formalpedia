-- Prove2me | Theorems.Thm_normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero
-- name    : normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:47.756713+00:00
-- url     : https://prove2.me/theorems/b3546bc7-3069-5906-8fc6-c4edd5565129
-- title:
--   normalized circle Integral inv pow smul resolvent eq zero: normalized circle Integral inv pow smul resolvent eq zero
-- statement:
--   Every strictly negative Laurent mode of the normalized centered resolvent
--   integral vanishes.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L403-L411
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L403-L411

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) (hn : 0 < n) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 R = 0 := by sorry
