-- Prove2me | Theorems.Thm_circleIntegral_eval_smul_resolvent_eq_two_pi_I_smul_aeval
-- name    : circleIntegral_eval_smul_resolvent_eq_two_pi_I_smul_aeval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:37:56.780309+00:00
-- url     : https://prove2.me/theorems/f8c8a4f5-0e3f-56b3-b212-d3c47be40abe
-- title:
--   circle Integral eval smul resolvent eq two pi I smul aeval: circle Integral eval smul resolvent eq two pi I smul aeval
-- statement:
--   Unnormalized polynomial operator Cauchy formula.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L462-L471
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L462-L471

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

theorem circleIntegral_eval_smul_resolvent_eq_two_pi_I_smul_aeval
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
      (2 * (Real.pi : ℂ) * I) • Polynomial.aeval A p := by sorry
