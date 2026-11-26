-- Prove2me | Theorems.Thm_norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers
-- name    : norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:35.70888+00:00
-- url     : https://prove2.me/theorems/528d1cf2-a8e7-4626-a1da-d3c4a547ed2e
-- title:
--   norm le two mul numerical Radius of mem centered Minimizers: norm le two mul numerical Radius of mem centered Minimizers
-- statement:
--   Every globally minimizing scalar center has modulus at most `2w(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L232-L240
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L232-L240

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

theorem norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers
    (A : E →L[ℂ] E) {c : ℂ}
    (hc : c ∈ centeredNumericalRadiusMinimizers A) :
    ‖c‖ ≤ 2 * numericalRadius A := by sorry
