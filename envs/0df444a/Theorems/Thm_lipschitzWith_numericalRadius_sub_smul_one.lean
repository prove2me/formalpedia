-- Prove2me | Theorems.Thm_lipschitzWith_numericalRadius_sub_smul_one
-- name    : lipschitzWith_numericalRadius_sub_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:46.331799+00:00
-- url     : https://prove2.me/theorems/c63084b9-e0e8-5897-b74e-02973c7f5115
-- title:
--   lipschitz With numerical Radius sub smul one: lipschitz With numerical Radius sub smul one
-- statement:
--   The numerical radius of `A - cI` is `1`-Lipschitz as a function of the
--   center `c`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L95-L100
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L95-L100

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

theorem lipschitzWith_numericalRadius_sub_smul_one (A : E →L[ℂ] E) :
    LipschitzWith 1 (fun c : ℂ => numericalRadius (A - c • 1)) := by sorry
