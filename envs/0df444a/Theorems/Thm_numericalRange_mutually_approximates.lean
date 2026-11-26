-- Prove2me | Theorems.Thm_numericalRange_mutually_approximates
-- name    : numericalRange_mutually_approximates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:16:04.524816+00:00
-- url     : https://prove2.me/theorems/6325fc9c-ae7b-42c2-bd54-b29963992817
-- title:
--   numerical Range mutually approximates: numerical Range mutually approximates
-- statement:
--   Symmetric form: the numerical ranges of `A` and `B` mutually
--   approximate one another within their operator-norm distance.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Stability.lean#L30-L42
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Stability.lean#L30-L42

import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Stability
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_mutually_approximates
    (A B : E →L[ℂ] E) :
    (∀ z ∈ numericalRange A,
        ∃ w ∈ numericalRange B, ‖z - w‖ ≤ ‖A - B‖) ∧
      (∀ w ∈ numericalRange B,
        ∃ z ∈ numericalRange A, ‖w - z‖ ≤ ‖A - B‖) := by sorry
