-- Prove2me | Theorems.Thm_numericalRadius_smul_one
-- name    : numericalRadius_smul_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:21.182982+00:00
-- url     : https://prove2.me/theorems/ec1f9b14-d7cb-4c8a-895a-36f564e6c3df
-- title:
--   numerical Radius smul one: numerical Radius smul one
-- statement:
--   A scalar operator has numerical radius equal to the scalar modulus.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L37-L39
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L37-L39

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

theorem numericalRadius_smul_one (c : ℂ) :
    numericalRadius (c • (1 : E →L[ℂ] E)) = ‖c‖ := by sorry
