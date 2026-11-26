-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
-- name    : crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:29.598076+00:00
-- url     : https://prove2.me/theorems/028565ae-f748-543e-af99-5497fe567276
-- title:
--   crouzeix Polynomial Scalar Companion ball eq eval zero: crouzeix Polynomial Scalar Companion ball eq eval zero
-- statement:
--   For every interior point of a centered disk, the scalar Crouzeix
--   companion is the constant `star (p.eval 0)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L72-L78
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean#L72-L78

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

theorem crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball 0 R hR) p z =
      star (Polynomial.eval 0 p) := by sorry
