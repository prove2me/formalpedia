-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_smul
-- name    : centeredNumericalRadiusMinimizers_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:39.299384+00:00
-- url     : https://prove2.me/theorems/61a930af-3567-5d2a-a077-0cf69431c713
-- title:
--   centered Numerical Radius Minimizers smul: centered Numerical Radius Minimizers smul
-- statement:
--   Multiplying an operator by a nonzero scalar multiplies every optimal
--   center by the same scalar.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L288-L316
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L288-L316

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

theorem centeredNumericalRadiusMinimizers_smul
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) :
    centeredNumericalRadiusMinimizers (a • A) =
      (fun c : ℂ => a * c) '' centeredNumericalRadiusMinimizers A := by sorry
