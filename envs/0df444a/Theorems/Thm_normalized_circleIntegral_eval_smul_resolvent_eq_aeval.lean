-- Prove2me | Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval
-- name    : normalized_circleIntegral_eval_smul_resolvent_eq_aeval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:04.122481+00:00
-- url     : https://prove2.me/theorems/74865117-abbe-5a72-acaa-7bcffa935ec1
-- title:
--   normalized circle Integral eval smul resolvent eq aeval: normalized circle Integral eval smul resolvent eq aeval
-- statement:
--   The polynomial operator Cauchy formula on any complex Hilbert space.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L450-L459
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L450-L459

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

theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
        Polynomial.aeval A p := by sorry
