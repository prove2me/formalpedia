-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_neg
-- name    : centeredNumericalRadiusMinimizers_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:21.902088+00:00
-- url     : https://prove2.me/theorems/22b1e557-749b-42b4-9b19-415782b34c8f
-- title:
--   centered Numerical Radius Minimizers neg: centered Numerical Radius Minimizers neg
-- statement:
--   Negating an operator negates every optimal scalar center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L320-L324
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L320-L324

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]

theorem centeredNumericalRadiusMinimizers_neg (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers (-A) =
      (fun c : ℂ => -c) '' centeredNumericalRadiusMinimizers A := by sorry
