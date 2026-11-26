-- Prove2me | Theorems.Thm_star_mem_centeredNumericalRadiusMinimizers_iff
-- name    : star_mem_centeredNumericalRadiusMinimizers_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:30.746827+00:00
-- url     : https://prove2.me/theorems/9724acb8-abec-5ee6-973e-1ad29abb47e8
-- title:
--   star mem centered Numerical Radius Minimizers iff: star mem centered Numerical Radius Minimizers iff
-- statement:
--   Membership among the optimal centers of a self-adjoint operator is
--   preserved and reflected by complex conjugation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L443-L456
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L443-L456

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

theorem star_mem_centeredNumericalRadiusMinimizers_iff
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (c : ℂ) :
    star c ∈ centeredNumericalRadiusMinimizers A ↔
      c ∈ centeredNumericalRadiusMinimizers A := by sorry
