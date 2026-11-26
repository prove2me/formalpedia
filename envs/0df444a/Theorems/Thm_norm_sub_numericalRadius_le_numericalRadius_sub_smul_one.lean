-- Prove2me | Theorems.Thm_norm_sub_numericalRadius_le_numericalRadius_sub_smul_one
-- name    : norm_sub_numericalRadius_le_numericalRadius_sub_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:46.122862+00:00
-- url     : https://prove2.me/theorems/e55d8d86-95f4-44f2-bccd-d2f5c68fccbc
-- title:
--   norm sub numerical Radius le numerical Radius sub smul one: norm sub numerical Radius le numerical Radius sub smul one
-- statement:
--   In particular, the centered numerical radius grows at least linearly in
--   the modulus of the center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L74-L80
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L74-L80

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

theorem norm_sub_numericalRadius_le_numericalRadius_sub_smul_one
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖c‖ - numericalRadius A ≤ numericalRadius (A - c • 1) := by sorry
