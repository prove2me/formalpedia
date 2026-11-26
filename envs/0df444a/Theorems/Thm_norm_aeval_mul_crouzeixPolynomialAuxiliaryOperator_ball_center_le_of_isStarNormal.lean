-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:50.592416+00:00
-- url     : https://prove2.me/theorems/7489abfa-0aa9-5b51-a9ed-58bd6a9d9594
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of is Star Normal: norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of is Star Normal
-- statement:
--   For a star-normal operator, an enclosing circle centered at a point of
--   the closed numerical range satisfies the sharp auxiliary product bound with
--   the closed numerical range itself as control set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProduct.lean#L86-L102
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProduct.lean#L86-L102

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_NormalProduct
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hc : c ∈ closure (numericalRange A)) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by sorry
