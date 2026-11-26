-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
-- name    : crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:43.589433+00:00
-- url     : https://prove2.me/theorems/8ae4c269-5199-5ee5-9c9b-38ca8f61fced
-- title:
--   crouzeix Polynomial Auxiliary Operator ball eq eval zero smul one of spectrum subset ball: crouzeix Polynomial Auxiliary Operator ball eq eval zero smul one of spectrum subset ball
-- statement:
--   If `spectrum ℂ A` lies in the centered open disk of radius `r`, the
--   conjugate-polynomial auxiliary operator on its boundary circle is the
--   constant operator `star (p.eval 0) • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliary.lean#L58-L131
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliary.lean#L58-L131

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball 0 r hr) p =
      star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E) := by sorry
