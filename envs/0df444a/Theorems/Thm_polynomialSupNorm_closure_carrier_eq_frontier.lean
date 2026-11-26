-- Prove2me | Theorems.Thm_polynomialSupNorm_closure_carrier_eq_frontier
-- name    : polynomialSupNorm_closure_carrier_eq_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:01.298895+00:00
-- url     : https://prove2.me/theorems/1baf6f42-0fbe-4b71-aa40-705ea3eb534a
-- title:
--   polynomial Sup Norm closure carrier eq frontier: polynomial Sup Norm closure carrier eq frontier
-- statement:
--   For a bounded smooth Jordan carrier, polynomial sup norms on its closure
--   and parametrized frontier agree exactly.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L63-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L63-L68

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
set_option autoImplicit false
open Complex Polynomial Set

theorem polynomialSupNorm_closure_carrier_eq_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier) :
    polynomialSupNorm p (closure Omega.carrier) =
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
