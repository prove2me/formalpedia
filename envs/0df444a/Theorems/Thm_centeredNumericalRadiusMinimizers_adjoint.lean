-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_adjoint
-- name    : centeredNumericalRadiusMinimizers_adjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:26:06.717243+00:00
-- url     : https://prove2.me/theorems/c9c55e3d-93de-4a25-9c5b-690f1fe89942
-- title:
--   centered Numerical Radius Minimizers adjoint: centered Numerical Radius Minimizers adjoint
-- statement:
--   Taking the adjoint conjugates every optimal scalar center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L363-L391
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L363-L391

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

theorem centeredNumericalRadiusMinimizers_adjoint [CompleteSpace E]
    (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers (A†) =
      (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A := by sorry
