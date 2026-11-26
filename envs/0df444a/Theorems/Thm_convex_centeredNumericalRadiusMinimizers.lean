-- Prove2me | Theorems.Thm_convex_centeredNumericalRadiusMinimizers
-- name    : convex_centeredNumericalRadiusMinimizers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:05.40061+00:00
-- url     : https://prove2.me/theorems/d96b02a3-f78f-5f74-b9b6-0db2d94b6dbb
-- title:
--   convex centered Numerical Radius Minimizers: convex centered Numerical Radius Minimizers
-- statement:
--   The set of globally minimizing scalar centers is convex.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L224-L229
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L224-L229

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

theorem convex_centeredNumericalRadiusMinimizers (A : E →L[ℂ] E) :
    Convex ℝ (centeredNumericalRadiusMinimizers A) := by sorry
