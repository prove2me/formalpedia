-- Prove2me | Theorems.Thm_spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- name    : spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:13.811+00:00
-- url     : https://prove2.me/theorems/4a9d04dd-85c1-4027-9a45-edeca8767802
-- title:
--   spectrum subset of is Compact nonempty convex of forall symmetrized bound: spectrum subset of is Compact nonempty convex of forall symmetrized bound
-- statement:
--   Universal circle symmetrization controlled by a compact nonempty convex
--   set forces that set to contain the spectrum of `A`.  An exterior spectral
--   value would yield a polynomial separator equal to one there and strictly
--   contractive on `K`, contradicting the corresponding zero-centered shifted
--   spectral disk.  The zero Hilbert space has empty spectrum and is handled
--   separately.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L758-L794
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L758-L794

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

theorem spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
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
    spectrum ℂ A ⊆ K := by sorry
