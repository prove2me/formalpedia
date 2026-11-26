-- Prove2me | Theorems.Thm_image_starRingEnd_centeredNumericalRadiusMinimizers_eq
-- name    : image_starRingEnd_centeredNumericalRadiusMinimizers_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:54.562217+00:00
-- url     : https://prove2.me/theorems/31662937-b054-5898-8891-5abf6ef92317
-- title:
--   image star Ring End centered Numerical Radius Minimizers eq: image star Ring End centered Numerical Radius Minimizers eq
-- statement:
--   The optimal centers of a self-adjoint operator are invariant under complex
--   conjugation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L434-L438
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L434-L438

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

theorem image_starRingEnd_centeredNumericalRadiusMinimizers_eq
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A =
      centeredNumericalRadiusMinimizers A := by sorry
