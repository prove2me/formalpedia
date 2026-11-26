-- Prove2me | Theorems.Thm_convex_setOf_numericalRadius_sub_smul_one_le
-- name    : convex_setOf_numericalRadius_sub_smul_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:57.849366+00:00
-- url     : https://prove2.me/theorems/dfb34c24-22ad-5ef5-b759-e2e337101489
-- title:
--   convex set Of numerical Radius sub smul one le: convex set Of numerical Radius sub smul one le
-- statement:
--   Every sublevel set of the centered numerical radius is convex.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L141-L145
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L141-L145

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

theorem convex_setOf_numericalRadius_sub_smul_one_le
    (A : E →L[ℂ] E) (r : ℝ) :
    Convex ℝ {c : ℂ | numericalRadius (A - c • 1) ≤ r} := by sorry
