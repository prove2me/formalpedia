-- Prove2me | Theorems.Thm_crouzeix_palencia_of_auxiliary_bounds
-- name    : crouzeix_palencia_of_auxiliary_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:59.454698+00:00
-- url     : https://prove2.me/theorems/bdab8c37-0b5a-5be0-95ad-0241f659d54d
-- title:
--   crouzeix palencia of auxiliary bounds: crouzeix palencia of auxiliary bounds
-- statement:
--   If every polynomial admits an auxiliary operator satisfying the two
--   Crouzeix--Palencia bounds, then the closure of the numerical range is a
--   `(1 + √2)`-polynomial spectral set.  This is the sorry-free assembly consumed
--   once L4.2c--e construct `G` and establish the bounds.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L822-L834
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L822-L834

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_auxiliary_bounds (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ‖Polynomial.aeval A p * G‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by sorry
