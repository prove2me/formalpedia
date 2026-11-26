-- Prove2me | Theorems.Thm_tendsto_numericalRadius_sub_smul_one_cocompact_atTop
-- name    : tendsto_numericalRadius_sub_smul_one_cocompact_atTop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:01.085803+00:00
-- url     : https://prove2.me/theorems/accba9ad-52fc-5ce5-963c-58188bb0e8df
-- title:
--   tendsto numerical Radius sub smul one cocompact at Top: tendsto numerical Radius sub smul one cocompact at Top
-- statement:
--   The centered numerical radius tends to infinity as the center leaves
--   compact subsets of the complex plane.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L167-L177
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L167-L177

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

theorem tendsto_numericalRadius_sub_smul_one_cocompact_atTop
    (A : E →L[ℂ] E) :
    Tendsto (fun c : ℂ => numericalRadius (A - c • 1))
      (cocompact ℂ) atTop := by sorry
