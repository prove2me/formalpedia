-- Prove2me | Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball
-- name    : norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:58.567801+00:00
-- url     : https://prove2.me/theorems/6a02c328-44f5-59ed-92d5-b1f4d7eee00b
-- title:
--   norm aeval add star crouzeix Polynomial Auxiliary Operator ball le of closure numerical Range subset ball: norm aeval add star crouzeix Polynomial Auxiliary Operator ball le of closure numerical Range
-- statement:
--   **Symmetrized Crouzeix–Palencia bound under the numerical-range hypothesis.** If the closure
--   of the numerical range lies in the open disk `ball 0 r`, then for the auxiliary operator `G` of
--   that disk, `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ r} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L122-L138
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L122-L138

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) r) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 r hr) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) r) := by sorry
