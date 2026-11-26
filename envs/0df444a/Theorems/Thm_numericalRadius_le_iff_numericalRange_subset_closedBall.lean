-- Prove2me | Theorems.Thm_numericalRadius_le_iff_numericalRange_subset_closedBall
-- name    : numericalRadius_le_iff_numericalRange_subset_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:32.416831+00:00
-- url     : https://prove2.me/theorems/c3135917-5e36-482a-9d04-122223fed7b6
-- title:
--   numerical Radius le iff numerical Range subset closed Ball: numerical Radius le iff numerical Range subset closed Ball
-- statement:
--   Closed-disk form of `numericalRadius_le_iff`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean#L26-L31
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean#L26-L31

import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusCharacterization
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_le_iff_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔
      numericalRange A ⊆ Metric.closedBall 0 r := by sorry
