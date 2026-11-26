-- Prove2me | Theorems.Thm_crouzeix_palencia_of_exists_convexThickening_smoothJordanRealization
-- name    : crouzeix_palencia_of_exists_convexThickening_smoothJordanRealization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:15:05.161649+00:00
-- url     : https://prove2.me/theorems/ebdf47e6-e709-41b1-87f6-355016b1ed1d
-- title:
--   crouzeix palencia of exists convex Thickening smooth Jordan Realization: crouzeix palencia of exists convex Thickening smooth Jordan Realization
-- statement:
--   Existence-only form of the explicit-thickening boundary: once each
--   thickening has a smooth Jordan realization, the sharp bound follows.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean#L49-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean#L49-L58

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_exists_convexThickening_smoothJordanRealization
    (A : E →L[ℂ] E)
    (hrealize : ∃ Omega : ℕ → SmoothJordanDomain,
      ∀ n, (Omega n).carrier =
        convexThickeningApprox (closure (numericalRange A)) n) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
