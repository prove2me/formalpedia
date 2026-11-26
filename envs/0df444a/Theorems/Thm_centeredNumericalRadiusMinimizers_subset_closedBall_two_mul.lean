-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_subset_closedBall_two_mul
-- name    : centeredNumericalRadiusMinimizers_subset_closedBall_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:04.174521+00:00
-- url     : https://prove2.me/theorems/cb0aad01-2bd7-5467-b8e1-6f724a96d2db
-- title:
--   centered Numerical Radius Minimizers subset closed Ball two mul: centered Numerical Radius Minimizers subset closed Ball two mul
-- statement:
--   The full minimizer set lies in the explicit disk of radius `2w(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L243-L249
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L243-L249

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

theorem centeredNumericalRadiusMinimizers_subset_closedBall_two_mul
    (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers A ⊆
      Metric.closedBall 0 (2 * numericalRadius A) := by sorry
