-- Prove2me | Theorems.Thm_isCompact_centeredNumericalRadiusMinimizers
-- name    : isCompact_centeredNumericalRadiusMinimizers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:07:58.509298+00:00
-- url     : https://prove2.me/theorems/2ae575f8-b55b-55fb-963a-fb4b52665858
-- title:
--   is Compact centered Numerical Radius Minimizers: is Compact centered Numerical Radius Minimizers
-- statement:
--   The set of globally minimizing scalar centers is compact.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L216-L221
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L216-L221

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

theorem isCompact_centeredNumericalRadiusMinimizers (A : E →L[ℂ] E) :
    IsCompact (centeredNumericalRadiusMinimizers A) := by sorry
