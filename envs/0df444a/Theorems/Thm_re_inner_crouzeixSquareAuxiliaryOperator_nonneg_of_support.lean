-- Prove2me | Theorems.Thm_re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
-- name    : re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:25.877296+00:00
-- url     : https://prove2.me/theorems/5e973394-af8c-46f5-a4e6-37cfdc48706b
-- title:
--   re inner crouzeix Square Auxiliary Operator nonneg of support: re inner crouzeix Square Auxiliary Operator nonneg of support
-- statement:
--   The scalar-square auxiliary operator has nonnegative quadratic real
--   part whenever the outward normal of the contour supports the numerical
--   range.  This is the signed half of double-layer positivity needed by the
--   product-remainder identity; it requires no triangle inequality and no
--   Cauchy mass normalization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L319-L460
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L319-L460

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    0 ≤ RCLike.re ⟪x,
      crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) x⟫_ℂ := by sorry
