-- Prove2me | Theorems.Thm_numericalRadius_le_iff
-- name    : numericalRadius_le_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:21.922809+00:00
-- url     : https://prove2.me/theorems/ac4a1146-d741-5abd-8c2f-6f5fba13f756
-- title:
--   numerical Radius le iff: numerical Radius le iff
-- statement:
--   A nonnegative real bounds the numerical radius exactly when it bounds the
--   modulus of every point in the numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean#L16-L23
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean#L16-L23

import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusCharacterization
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_le_iff
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔ ∀ z ∈ numericalRange A, ‖z‖ ≤ r := by sorry
