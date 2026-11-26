-- Prove2me | Theorems.Thm_crouzeix_palencia_of_auxiliary_re_inner_lower_bounds
-- name    : crouzeix_palencia_of_auxiliary_re_inner_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:08.914575+00:00
-- url     : https://prove2.me/theorems/d29a2a87-bb59-440f-baa2-916445eb81f1
-- title:
--   crouzeix palencia of auxiliary re inner lower bounds: crouzeix palencia of auxiliary re inner lower bounds
-- statement:
--   If every polynomial admits an auxiliary operator with the symmetrized
--   bound and the sharp one-sided lower bound on the real part of its product,
--   then the closed numerical range is a `(1 + √2)`-polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L803-L816
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L803-L816

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_auxiliary_re_inner_lower_bounds (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ∀ x : E, ‖x‖ = 1 →
        -(polynomialSupNorm p (closure (numericalRange A)) ^ 2) ≤
          RCLike.re ⟪x, (Polynomial.aeval A p * G) x⟫_ℂ) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by sorry
