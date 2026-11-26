-- Prove2me | Theorems.Thm_continuous_numericalRadius_sub_smul_one
-- name    : continuous_numericalRadius_sub_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:43.538479+00:00
-- url     : https://prove2.me/theorems/37fd2412-8463-5ca8-a2e6-58e7d5ce3a55
-- title:
--   continuous numerical Radius sub smul one: continuous numerical Radius sub smul one
-- statement:
--   The centered numerical radius depends continuously on the center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L103-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L103-L105

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

theorem continuous_numericalRadius_sub_smul_one (A : E →L[ℂ] E) :
    Continuous (fun c : ℂ => numericalRadius (A - c • 1)) := by sorry
