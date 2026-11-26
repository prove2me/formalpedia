-- Prove2me | Theorems.Thm_abs_numericalRadius_sub_smul_one_sub_le
-- name    : abs_numericalRadius_sub_smul_one_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:07:47.074144+00:00
-- url     : https://prove2.me/theorems/ab2f2029-c990-55c5-b250-bf3aeb1dd0b4
-- title:
--   abs numerical Radius sub smul one sub le: abs numerical Radius sub smul one sub le
-- statement:
--   Subtracting a scalar operator changes numerical radius by at most the
--   scalar modulus.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L51-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L51-L55

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

theorem abs_numericalRadius_sub_smul_one_sub_le
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A - c • 1) - numericalRadius A| ≤ ‖c‖ := by sorry
