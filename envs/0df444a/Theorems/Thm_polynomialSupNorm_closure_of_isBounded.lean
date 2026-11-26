-- Prove2me | Theorems.Thm_polynomialSupNorm_closure_of_isBounded
-- name    : polynomialSupNorm_closure_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:35.540866+00:00
-- url     : https://prove2.me/theorems/457dd4be-e313-4395-b6c0-996407049f1e
-- title:
--   polynomial Sup Norm closure of is Bounded: polynomial Sup Norm closure of is Bounded
-- statement:
--   Taking the closure of a bounded planar set does not change a polynomial's
--   sup norm.  The empty-set case is included.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L72-L89
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L72-L89

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
set_option autoImplicit false
open Complex Polynomial Set

theorem polynomialSupNorm_closure_of_isBounded
    (p : Polynomial ℂ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    polynomialSupNorm p (closure X) = polynomialSupNorm p X := by sorry
