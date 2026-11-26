-- Prove2me | Theorems.Thm_isCompact_setOf_numericalRadius_sub_smul_one_le
-- name    : isCompact_setOf_numericalRadius_sub_smul_one_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:04.71363+00:00
-- url     : https://prove2.me/theorems/d185427a-37d8-416a-841b-4ad8c6e37069
-- title:
--   is Compact set Of numerical Radius sub smul one le: is Compact set Of numerical Radius sub smul one le
-- statement:
--   Every sublevel set of the centered numerical radius is compact.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L148-L163
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L148-L163

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

theorem isCompact_setOf_numericalRadius_sub_smul_one_le
    (A : E →L[ℂ] E) (r : ℝ) :
    IsCompact {c : ℂ | numericalRadius (A - c • 1) ≤ r} := by sorry
