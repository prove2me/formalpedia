-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_ball_le_polynomialSupNorm_closedBall
-- name    : norm_crouzeixPolynomialScalarCompanion_ball_le_polynomialSupNorm_closedBall
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:52:22.693951+00:00
-- url     : https://prove2.me/theorems/c2c6af93-3a54-44a5-89af-89b2bdce88df
-- title:
--   norm crouzeix Polynomial Scalar Companion ball le polynomial Sup Norm closed Ball: norm crouzeix Polynomial Scalar Companion ball le polynomial Sup Norm closed Ball
-- statement:
--   The scalar companion on a centered disk is contractive for the polynomial
--   sup norm on the closed disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L97-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L97-L105

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_ball_le_polynomialSupNorm_closedBall
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball 0 R hR) p z‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by sorry
