-- Prove2me | Theorems.Thm_normalized_circleIntegral_resolvent_eq_one
-- name    : normalized_circleIntegral_resolvent_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:10.883377+00:00
-- url     : https://prove2.me/theorems/fbabc5ae-ac4d-43d1-8df2-3cf50cbf0c9c
-- title:
--   normalized circle Integral resolvent eq one: normalized circle Integral resolvent eq one
-- statement:
--   The normalized resolvent integral for an operator on any complex Hilbert
--   space, including the zero space.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L415-L423
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L415-L423

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

theorem normalized_circleIntegral_resolvent_eq_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 R =
      (1 : E →L[ℂ] E) := by sorry
