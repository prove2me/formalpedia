-- Prove2me | Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt
-- name    : circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:04:56.12382+00:00
-- url     : https://prove2.me/theorems/bfc991a6-935a-50ea-aa2e-c50f933d4689
-- title:
--   circle Integral resolvent eq two pi I smul one of norm sub smul one lt: circle Integral resolvent eq two pi I smul one of norm sub smul one lt
-- statement:
--   The unnormalized resolvent Cauchy identity on a circle centered at `c`.
--   The hypothesis is the translated Neumann-series condition
--   `‖A - c • 1‖ < R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L486-L509
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L486-L509

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

theorem circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : ‖A - c • (1 : E →L[ℂ] E)‖ < R) :
    circleIntegral (resolvent A) c R =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
