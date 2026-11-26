-- Prove2me | Theorems.Thm_neg_star_mem_centeredNumericalRadiusMinimizers_iff
-- name    : neg_star_mem_centeredNumericalRadiusMinimizers_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:26:16.529826+00:00
-- url     : https://prove2.me/theorems/ddf329d6-ddbe-4a97-b887-8a5370540876
-- title:
--   neg star mem centered Numerical Radius Minimizers iff: neg star mem centered Numerical Radius Minimizers iff
-- statement:
--   The optimal centers of a skew-adjoint operator are preserved and
--   reflected by reflection across the imaginary axis.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L503-L531
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L503-L531

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

theorem neg_star_mem_centeredNumericalRadiusMinimizers_iff
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) (c : ℂ) :
    -star c ∈ centeredNumericalRadiusMinimizers A ↔
      c ∈ centeredNumericalRadiusMinimizers A := by sorry
