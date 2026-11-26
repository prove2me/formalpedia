-- Prove2me | Theorems.Thm_norm_eval_boundaryParam_le_polynomialSupNorm_frontier
-- name    : norm_eval_boundaryParam_le_polynomialSupNorm_frontier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:10.390158+00:00
-- url     : https://prove2.me/theorems/27cdfda2-7add-4303-9ac0-6ad0248ac5c6
-- title:
--   norm eval boundary Param le polynomial Sup Norm frontier: norm eval boundary Param le polynomial Sup Norm frontier
-- statement:
--   Every value of a polynomial on the parametrized boundary is bounded by
--   its polynomial sup norm on the domain frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L71-L78
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L71-L78

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_eval_boundaryParam_le_polynomialSupNorm_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (t : ℝ) :
    ‖Polynomial.eval (Omega.boundaryParam t) p‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
