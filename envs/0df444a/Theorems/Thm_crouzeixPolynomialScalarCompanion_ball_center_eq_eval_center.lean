-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
-- name    : crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:33.559524+00:00
-- url     : https://prove2.me/theorems/d0a63e79-f0b2-4bc9-bd3b-6fe708bc61ee
-- title:
--   crouzeix Polynomial Scalar Companion ball center eq eval center: crouzeix Polynomial Scalar Companion ball center eq eval center
-- statement:
--   For every interior point of a disk, the scalar Crouzeix companion is the
--   constant `star (p.eval c)`, where `c` is the center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L40-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L40-L68

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

theorem crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z =
      star (Polynomial.eval c p) := by sorry
