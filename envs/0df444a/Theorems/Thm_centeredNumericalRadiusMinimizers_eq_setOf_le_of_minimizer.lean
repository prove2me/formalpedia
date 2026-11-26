-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer
-- name    : centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:53.331942+00:00
-- url     : https://prove2.me/theorems/4fbae71d-c0fe-425b-a3f7-881389fe0a53
-- title:
--   centered Numerical Radius Minimizers eq set Of le of minimizer: centered Numerical Radius Minimizers eq set Of le of minimizer
-- statement:
--   Once a minimizing center is fixed, the full minimizer set is its
--   centered-radius sublevel set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L196-L207
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L196-L207

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

theorem centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer
    (A : E →L[ℂ] E) {c : ℂ}
    (hc : ∀ d : ℂ,
      numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) :
    centeredNumericalRadiusMinimizers A =
      {d : ℂ |
        numericalRadius (A - d • 1) ≤ numericalRadius (A - c • 1)} := by sorry
