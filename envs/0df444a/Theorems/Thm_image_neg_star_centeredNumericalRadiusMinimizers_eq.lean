-- Prove2me | Theorems.Thm_image_neg_star_centeredNumericalRadiusMinimizers_eq
-- name    : image_neg_star_centeredNumericalRadiusMinimizers_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:45.108527+00:00
-- url     : https://prove2.me/theorems/cc0158fc-7111-4f48-bc02-db2279b15583
-- title:
--   image neg star centered Numerical Radius Minimizers eq: image neg star centered Numerical Radius Minimizers eq
-- statement:
--   Reflection across the imaginary axis fixes the optimal-center set of a
--   skew-adjoint operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L536-L548
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L536-L548

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

theorem image_neg_star_centeredNumericalRadiusMinimizers_eq
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    (fun c : ℂ => -star c) '' centeredNumericalRadiusMinimizers A =
      centeredNumericalRadiusMinimizers A := by sorry
