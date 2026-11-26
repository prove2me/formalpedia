-- Prove2me | Theorems.Thm_exists_tendsto_polynomial_companions_ball_center
-- name    : exists_tendsto_polynomial_companions_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:17.956774+00:00
-- url     : https://prove2.me/theorems/cf539958-529e-5966-bfed-012959b5b625
-- title:
--   exists tendsto polynomial companions ball center: exists tendsto polynomial companions ball center
-- statement:
--   On an enclosing disk, the polynomial companions required by the
--   published approximation route can be chosen to be a constant sequence.  It
--   is exactly contractive for the closed-disk sup norm and its evaluations at
--   `A` converge (indeed, are equal) to the canonical auxiliary operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L654-L673
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L654-L673

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_tendsto_polynomial_companions_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) (Metric.closedBall c R) ≤
        polynomialSupNorm p (Metric.closedBall c R)) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
        (nhds (crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p)) := by sorry
