-- Prove2me | Theorems.Thm_crouzeix_palencia_of_auxiliary_inner_bounds
-- name    : crouzeix_palencia_of_auxiliary_inner_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:03.654802+00:00
-- url     : https://prove2.me/theorems/6c173695-ec22-43df-8643-7a9a9c586caa
-- title:
--   crouzeix palencia of auxiliary inner bounds: crouzeix palencia of auxiliary inner bounds
-- statement:
--   If every polynomial admits an auxiliary operator with the symmetrized
--   bound and the sharp product bound only on unit-vector quadratic forms, then
--   the closed numerical range is a `(1 + √2)`-polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L785-L798
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L785-L798

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_auxiliary_inner_bounds (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ∀ x : E, ‖x‖ = 1 →
        ‖⟪x, (Polynomial.aeval A p * G) x⟫_ℂ‖ ≤
          polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by sorry
