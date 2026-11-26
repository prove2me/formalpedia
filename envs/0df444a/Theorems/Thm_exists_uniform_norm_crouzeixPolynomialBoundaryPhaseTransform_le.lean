-- Prove2me | Theorems.Thm_exists_uniform_norm_crouzeixPolynomialBoundaryPhaseTransform_le
-- name    : exists_uniform_norm_crouzeixPolynomialBoundaryPhaseTransform_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:43:33.669357+00:00
-- url     : https://prove2.me/theorems/3a049c89-7c2b-578c-b4ab-ac84924453f5
-- title:
--   exists uniform norm crouzeix Polynomial Boundary Phase Transform le: exists uniform norm crouzeix Polynomial Boundary Phase Transform le
-- statement:
--   One nonnegative domain-only speed constant controls every boundary phase
--   transform, uniformly in its base point and polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L459-L469
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L459-L469

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem exists_uniform_norm_crouzeixPolynomialBoundaryPhaseTransform_le
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (xi : ℂ) (q : Polynomial ℂ),
      ‖crouzeixPolynomialBoundaryPhaseTransform Omega xi q‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm q (frontier Omega.carrier))) := by sorry
