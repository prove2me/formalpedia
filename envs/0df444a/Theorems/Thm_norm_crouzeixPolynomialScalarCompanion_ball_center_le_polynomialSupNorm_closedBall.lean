-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
-- name    : norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:52.630801+00:00
-- url     : https://prove2.me/theorems/77734658-bcc2-4e5d-a708-de02e572e917
-- title:
--   norm crouzeix Polynomial Scalar Companion ball center le polynomial Sup Norm closed Ball: norm crouzeix Polynomial Scalar Companion ball center le polynomial Sup Norm closed Ball
-- statement:
--   The scalar companion on an arbitrary disk is contractive for the
--   polynomial sup norm on the corresponding closed disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L82-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L82-L93

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    ‖crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) := by sorry
