-- Prove2me | Theorems.Thm_exists_continuous_scalarCompanion_approximation_ball_center
-- name    : exists_continuous_scalarCompanion_approximation_ball_center
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:53:40.99345+00:00
-- url     : https://prove2.me/theorems/39ca425e-5985-44c3-8f60-fcc69b062429
-- title:
--   exists continuous scalar Companion approximation ball center: exists continuous scalar Companion approximation ball center
-- statement:
--   The disk model supplies all scalar-companion inputs used by the published
--   approximation route at once.  The canonical closed extension is continuous
--   on the boundary and sharply contractive on the closed disk; the constant
--   polynomial sequence agrees with it exactly, and its auxiliary contour is the
--   conjugate-polynomial auxiliary operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L594-L631
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L594-L631

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

theorem exists_continuous_scalarCompanion_approximation_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
      ContinuousOn g
          ((SmoothJordanDomain.ball c R hR).boundaryParam ''
            Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ Metric.closedBall c R,
        ‖g z‖ ≤ polynomialSupNorm p (Metric.closedBall c R)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ Metric.closedBall c R →
        ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) g =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p := by sorry
