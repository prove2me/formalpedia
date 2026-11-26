-- Prove2me | Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one
-- name    : circleIntegral_resolvent_eq_two_pi_I_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:10.00323+00:00
-- url     : https://prove2.me/theorems/1e15d5db-d880-479d-b0c4-104bc4380012
-- title:
--   circle Integral resolvent eq two pi I smul one: circle Integral resolvent eq two pi I smul one
-- statement:
--   Unnormalized form of the resolvent Cauchy identity, matching the mass
--   hypothesis used by the double-layer normalization lemmas.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L427-L436
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L427-L436

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

theorem circleIntegral_resolvent_eq_two_pi_I_smul_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    circleIntegral (resolvent A) 0 R =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
