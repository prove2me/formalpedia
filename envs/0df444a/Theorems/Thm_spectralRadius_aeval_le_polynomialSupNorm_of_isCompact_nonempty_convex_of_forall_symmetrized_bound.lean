-- Prove2me | Theorems.Thm_spectralRadius_aeval_le_polynomialSupNorm_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- name    : spectralRadius_aeval_le_polynomialSupNorm_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:19.964826+00:00
-- url     : https://prove2.me/theorems/11bd2d43-be4e-51ce-91d9-eb020b798084
-- title:
--   spectral Radius aeval le polynomial Sup Norm of is Compact nonempty convex of forall symmetrized bound: spectral Radius aeval le polynomial Sup Norm of is Compact nonempty convex of forall symmetrized
-- statement:
--   Universal circle symmetrization over a compact nonempty convex control set
--   gives the sharp factor-one spectral-radius bound for every polynomial value.
--   This is a spectral conclusion and therefore also covers the zero Hilbert
--   space.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L648-L665
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L648-L665

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

theorem spectralRadius_aeval_le_polynomialSupNorm_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) :
    spectralRadius ℂ (Polynomial.aeval A p) ≤
      ((polynomialSupNorm p K).toNNReal : ENNReal) := by sorry
