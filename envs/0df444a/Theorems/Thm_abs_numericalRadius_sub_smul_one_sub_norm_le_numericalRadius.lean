-- Prove2me | Theorems.Thm_abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius
-- name    : abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:26:44.328268+00:00
-- url     : https://prove2.me/theorems/42174f66-c6a9-4452-a7dc-93d18a8966cf
-- title:
--   abs numerical Radius sub smul one sub norm le numerical Radius: abs numerical Radius sub smul one sub norm le numerical Radius
-- statement:
--   The centered numerical radius differs from the modulus of its center by
--   at most `w(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L59-L70
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L59-L70

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

theorem abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A - c • 1) - ‖c‖| ≤ numericalRadius A := by sorry
