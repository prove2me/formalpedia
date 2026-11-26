-- Prove2me | Theorems.Thm_polynomialSupNorm_carrier_eq_frontier
-- name    : polynomialSupNorm_carrier_eq_frontier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:39:28.282574+00:00
-- url     : https://prove2.me/theorems/cf6f8839-a387-42da-ab69-825a3b094bfc
-- title:
--   polynomial Sup Norm carrier eq frontier: polynomial Sup Norm carrier eq frontier
-- statement:
--   For a bounded smooth Jordan carrier, polynomial sup norms on the carrier
--   and its parametrized frontier agree exactly.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L93-L99
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean#L93-L99

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
set_option autoImplicit false
open Complex Polynomial Set

theorem polynomialSupNorm_carrier_eq_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier) :
    polynomialSupNorm p Omega.carrier =
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
