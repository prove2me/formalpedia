-- Prove2me | Theorems.Thm_spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- name    : spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:49.935128+00:00
-- url     : https://prove2.me/theorems/1672e385-f5f2-5390-8e32-8ed75f974f7b
-- title:
--   spectral Radius aeval sub smul one le polynomial Sup Norm sub C of is Compact nonempty convex of forall symmetrized bound: spectral Radius aeval sub smul one le polynomial Sup Norm sub C of is Compact
-- statement:
--   Universal circle symmetrization over a compact nonempty convex control set
--   gives a sharp factor-one spectral-radius bound after every scalar shift.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L615-L642
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L615-L642

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

theorem spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
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
    (p : Polynomial ℂ) (b : ℂ) :
    spectralRadius ℂ
        (Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) ≤
      ((polynomialSupNorm (p - Polynomial.C b) K).toNNReal : ENNReal) := by sorry
