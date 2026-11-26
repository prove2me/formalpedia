-- Prove2me | Theorems.Thm_spectralRadius_aeval_le_polynomialSupNorm_closure_numericalRange_of_forall_symmetrized_bound
-- name    : spectralRadius_aeval_le_polynomialSupNorm_closure_numericalRange_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:59:37.031317+00:00
-- url     : https://prove2.me/theorems/27e9f210-fadd-5654-94e7-d30ee0f2dabd
-- title:
--   spectral Radius aeval le polynomial Sup Norm closure numerical Range of forall symmetrized bound: spectral Radius aeval le polynomial Sup Norm closure numerical Range of forall symmetrized bound
-- statement:
--   Universal circle symmetrization controlled by the closed numerical range
--   gives the sharp factor-one spectral-radius bound for every polynomial value,
--   including on the zero Hilbert space.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L735-L750
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L735-L750

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem spectralRadius_aeval_le_polynomialSupNorm_closure_numericalRange_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A)))
    (p : Polynomial ℂ) :
    spectralRadius ℂ (Polynomial.aeval A p) ≤
      ((polynomialSupNorm p (closure (numericalRange A))).toNNReal : ENNReal) := by sorry
