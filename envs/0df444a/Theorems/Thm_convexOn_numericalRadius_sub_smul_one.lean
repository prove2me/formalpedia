-- Prove2me | Theorems.Thm_convexOn_numericalRadius_sub_smul_one
-- name    : convexOn_numericalRadius_sub_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:05.241981+00:00
-- url     : https://prove2.me/theorems/bfb65c8e-af06-444f-93ea-f2e781879a2a
-- title:
--   convex On numerical Radius sub smul one: convex On numerical Radius sub smul one
-- statement:
--   The numerical radius of the scalar translate `A-cI` is convex as a
--   function of the center `c`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L110-L137
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L110-L137

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

theorem convexOn_numericalRadius_sub_smul_one (A : E →L[ℂ] E) :
    ConvexOn ℝ Set.univ (fun c : ℂ => numericalRadius (A - c • 1)) := by sorry
