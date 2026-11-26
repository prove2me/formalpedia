-- Prove2me | Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball_center
-- name    : norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:42.207953+00:00
-- url     : https://prove2.me/theorems/767a3a8e-0ef1-4fb8-9616-25f11304cf86
-- title:
--   norm aeval add star crouzeix Polynomial Auxiliary Operator ball le of closure numerical Range subset ball center: norm aeval add star crouzeix Polynomial Auxiliary Operator ball le of closure numerica
-- statement:
--   **Symmetrized Crouzeix–Palencia bound for an arbitrary disk containing the numerical range.**
--   If `closure W(A) ⊆ ball c r`, then for the auxiliary operator `G` of that disk,
--   `‖p(A) + G†‖ ≤ 2 * sup_{|z - c| ≤ r} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L231-L248
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L231-L248

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball_center
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c r hr) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall c r) := by sorry
