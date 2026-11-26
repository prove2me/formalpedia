-- Prove2me | Theorems.Thm_polynomialSupNorm_closure_eq_frontier_of_isBounded
-- name    : polynomialSupNorm_closure_eq_frontier_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:00.379488+00:00
-- url     : https://prove2.me/theorems/f98c81c5-49c1-4cb8-9aa3-42eca805eff0
-- title:
--   polynomial Sup Norm closure eq frontier of is Bounded: polynomial Sup Norm closure eq frontier of is Bounded
-- statement:
--   On a bounded planar set, a polynomial's sup norm on the closure equals
--   its sup norm on the frontier.  The empty-set case is included.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L46-L59
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L46-L59

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
set_option autoImplicit false
open Complex Polynomial Set

theorem polynomialSupNorm_closure_eq_frontier_of_isBounded
    (p : Polynomial ℂ) {U : Set ℂ} (hU : Bornology.IsBounded U) :
    polynomialSupNorm p (closure U) = polynomialSupNorm p (frontier U) := by sorry
