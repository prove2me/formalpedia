-- Prove2me | Theorems.Thm_closure_numericalRange_subset_ball_of_norm_lt
-- name    : closure_numericalRange_subset_ball_of_norm_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:01.099918+00:00
-- url     : https://prove2.me/theorems/81bf33d4-fa7e-5cde-b84a-618285e1fe34
-- title:
--   closure numerical Range subset ball of norm lt: closure numerical Range subset ball of norm lt
-- statement:
--   If `‖A‖ < R`, the closure of the numerical range lies in the open disk `ball 0 R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L107-L113
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L107-L113

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]

theorem closure_numericalRange_subset_ball_of_norm_lt (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) R := by sorry
