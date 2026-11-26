-- Prove2me | Theorems.Thm_exists_real_center_minimizing_numericalRadius_of_isSelfAdjoint
-- name    : exists_real_center_minimizing_numericalRadius_of_isSelfAdjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:08:43.791732+00:00
-- url     : https://prove2.me/theorems/4e372ccd-42ac-4028-a6f6-da41251c72d3
-- title:
--   exists real center minimizing numerical Radius of is Self Adjoint: exists real center minimizing numerical Radius of is Self Adjoint
-- statement:
--   For a self-adjoint operator, the centered numerical radius attains its
--   global minimum at a real center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L493-L498
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L493-L498

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

theorem exists_real_center_minimizing_numericalRadius_of_isSelfAdjoint
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, ∀ c : ℂ,
      numericalRadius (A - (r : ℂ) • 1) ≤
        numericalRadius (A - c • 1) := by sorry
