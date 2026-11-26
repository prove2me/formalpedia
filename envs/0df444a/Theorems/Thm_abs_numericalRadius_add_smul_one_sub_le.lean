-- Prove2me | Theorems.Thm_abs_numericalRadius_add_smul_one_sub_le
-- name    : abs_numericalRadius_add_smul_one_sub_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:26:49.548804+00:00
-- url     : https://prove2.me/theorems/45726378-fa75-45a5-9307-1c056c789516
-- title:
--   abs numerical Radius add smul one sub le: abs numerical Radius add smul one sub le
-- statement:
--   Adding a scalar operator changes numerical radius by at most the scalar
--   modulus.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L43-L47
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L43-L47

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

theorem abs_numericalRadius_add_smul_one_sub_le
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A + c • 1) - numericalRadius A| ≤ ‖c‖ := by sorry
