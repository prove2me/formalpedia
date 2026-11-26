-- Prove2me | Theorems.Thm_polynomialSupNorm_mono_of_isCompact
-- name    : polynomialSupNorm_mono_of_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:12.563005+00:00
-- url     : https://prove2.me/theorems/991d689c-298e-5ea0-8328-a7774cff425c
-- title:
--   polynomial Sup Norm mono of is Compact: polynomial Sup Norm mono of is Compact
-- statement:
--   Polynomial sup norms are monotone under set inclusion whenever the values
--   on the larger set are bounded, in particular when that set is compact.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L45-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L45-L54

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
set_option autoImplicit false
open Filter Polynomial Set

theorem polynomialSupNorm_mono_of_isCompact
    (p : Polynomial ℂ) {K L : Set ℂ} (hKL : K ⊆ L) (hL : IsCompact L) :
    polynomialSupNorm p K ≤ polynomialSupNorm p L := by sorry
