-- Prove2me | Theorems.Thm_tendsto_pow_sub_smul_one_atTop_nhds_zero_of_numericalRadius_lt_one
-- name    : tendsto_pow_sub_smul_one_atTop_nhds_zero_of_numericalRadius_lt_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:29.064469+00:00
-- url     : https://prove2.me/theorems/ebc10841-3c87-4848-889c-61a8480e50b6
-- title:
--   tendsto pow sub smul one at Top nhds zero of numerical Radius lt one: tendsto pow sub smul one at Top nhds zero of numerical Radius lt one
-- statement:
--   If a centered numerical radius is strictly less than one, the powers of
--   the centered operator converge to zero in operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L142-L149
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean#L142-L149

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

theorem tendsto_pow_sub_smul_one_atTop_nhds_zero_of_numericalRadius_lt_one
    (A : E →L[ℂ] E) (c : ℂ)
    (hA : numericalRadius (A - c • (1 : E →L[ℂ] E)) < 1) :
    Filter.Tendsto
      (fun n : ℕ => (A - c • (1 : E →L[ℂ] E)) ^ n)
      Filter.atTop (nhds 0) := by sorry
