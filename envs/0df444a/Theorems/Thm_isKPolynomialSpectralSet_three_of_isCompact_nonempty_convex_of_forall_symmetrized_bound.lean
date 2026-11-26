-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- name    : isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:01:26.53535+00:00
-- url     : https://prove2.me/theorems/c9000dc8-dbed-45d1-a4fe-576fbaa5c402
-- title:
--   is KPolynomial Spectral Set three of is Compact nonempty convex of forall symmetrized bound: is KPolynomial Spectral Set three of is Compact nonempty convex of forall symmetrized bound
-- statement:
--   Universal circle symmetrization controlled by a compact nonempty convex
--   set makes that set a `3`-polynomial spectral set.  Spectrum containment comes
--   from shifted moments and polynomial separation; the norm estimate is the
--   zero-shift bound `2m + |p(c)| ≤ 3m` after center alignment.  The zero Hilbert
--   space is discharged separately.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L938-L979
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L938-L979

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

theorem isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    IsKPolynomialSpectralSet A 3 K := by sorry
