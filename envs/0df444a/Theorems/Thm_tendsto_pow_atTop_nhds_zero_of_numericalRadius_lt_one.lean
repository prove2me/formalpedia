-- Prove2me | Theorems.Thm_tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one
-- name    : tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:47:39.956508+00:00
-- url     : https://prove2.me/theorems/b105d287-8935-4f96-921a-273b3941e16e
-- title:
--   tendsto pow at Top nhds zero of numerical Radius lt one: tendsto pow at Top nhds zero of numerical Radius lt one
-- statement:
--   If the numerical radius is strictly less than one, the operator powers
--   converge to zero in operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L128-L138
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L128-L138

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one
    (A : E →L[ℂ] E) (hA : numericalRadius A < 1) :
    Filter.Tendsto (fun n : ℕ => A ^ n) Filter.atTop (nhds 0) := by sorry
