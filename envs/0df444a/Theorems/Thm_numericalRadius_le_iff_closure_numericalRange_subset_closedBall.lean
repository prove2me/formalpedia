-- Prove2me | Theorems.Thm_numericalRadius_le_iff_closure_numericalRange_subset_closedBall
-- name    : numericalRadius_le_iff_closure_numericalRange_subset_closedBall
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:15:30.824852+00:00
-- url     : https://prove2.me/theorems/92c9c1c2-a25f-4cf4-b2f3-bb49725f5e62
-- title:
--   numerical Radius le iff closure numerical Range subset closed Ball: numerical Radius le iff closure numerical Range subset closed Ball
-- statement:
--   The same disk characterization holds for the closed numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean#L34-L45
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean#L34-L45

import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusCharacterization
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_le_iff_closure_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔
      closure (numericalRange A) ⊆ Metric.closedBall 0 r := by sorry
