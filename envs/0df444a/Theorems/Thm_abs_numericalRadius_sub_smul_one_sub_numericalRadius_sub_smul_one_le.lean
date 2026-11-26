-- Prove2me | Theorems.Thm_abs_numericalRadius_sub_smul_one_sub_numericalRadius_sub_smul_one_le
-- name    : abs_numericalRadius_sub_smul_one_sub_numericalRadius_sub_smul_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:50.953852+00:00
-- url     : https://prove2.me/theorems/af0a149c-e5be-47df-ad8e-afcd083b5c69
-- title:
--   abs numerical Radius sub smul one sub numerical Radius sub smul one le: abs numerical Radius sub smul one sub numerical Radius sub smul one le
-- statement:
--   Centering at two scalars changes numerical radius by at most the distance
--   between the centers.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L84-L91
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L84-L91

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

theorem abs_numericalRadius_sub_smul_one_sub_numericalRadius_sub_smul_one_le
    (A : E →L[ℂ] E) (c d : ℂ) :
    |numericalRadius (A - c • 1) - numericalRadius (A - d • 1)| ≤ ‖c - d‖ := by sorry
