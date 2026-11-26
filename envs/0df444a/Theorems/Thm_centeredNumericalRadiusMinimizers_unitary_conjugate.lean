-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_unitary_conjugate
-- name    : centeredNumericalRadiusMinimizers_unitary_conjugate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:07.65293+00:00
-- url     : https://prove2.me/theorems/0a8c6f4f-6e65-4b18-b2f3-1d59807034ac
-- title:
--   centered Numerical Radius Minimizers unitary conjugate: centered Numerical Radius Minimizers unitary conjugate
-- statement:
--   Unitary conjugation preserves every optimal scalar center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L395-L418
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L395-L418

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

theorem centeredNumericalRadiusMinimizers_unitary_conjugate [CompleteSpace E]
    (A U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) :
    centeredNumericalRadiusMinimizers (U† * A * U) =
      centeredNumericalRadiusMinimizers A := by sorry
