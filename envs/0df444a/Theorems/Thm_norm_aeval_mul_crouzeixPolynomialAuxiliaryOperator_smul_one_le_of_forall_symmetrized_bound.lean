-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul_one_le_of_forall_symmetrized_bound
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul_one_le_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:04:17.914651+00:00
-- url     : https://prove2.me/theorems/07a6e09f-651f-4d8a-8bcb-1de612a7431d
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator smul one le of forall symmetrized bound: norm aeval mul crouzeix Polynomial Auxiliary Operator smul one le of forall symmetrized bound
-- statement:
--   On a scalar operator, the universal sharp symmetrized family forces
--   circle alignment and therefore implies the literal sharp auxiliary product
--   bound for every polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductSymmetrizedAlignment.lean#L110-L138
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductSymmetrizedAlignment.lean#L110-L138

import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_ProductSymmetrizedAlignment
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul_one_le_of_forall_symmetrized_bound
    (a c : ℂ) {R : ℝ}
    (hA : ‖a • (1 : E →L[ℂ] E) - c • 1‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval (a • (1 : E →L[ℂ] E)) q +
          star (crouzeixPolynomialAuxiliaryOperator
            (a • (1 : E →L[ℂ] E))
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q
          (closure (numericalRange (a • (1 : E →L[ℂ] E)))))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval (a • (1 : E →L[ℂ] E)) p *
        crouzeixPolynomialAuxiliaryOperator
          (a • (1 : E →L[ℂ] E))
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p
        (closure (numericalRange (a • (1 : E →L[ℂ] E)))) ^ 2 := by sorry
