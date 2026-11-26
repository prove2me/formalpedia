-- Prove2me | Theorems.Thm_numericalRadius_adjoint_comp_comp_le
-- name    : numericalRadius_adjoint_comp_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:35.017575+00:00
-- url     : https://prove2.me/theorems/6a099725-33b9-5d23-a6b0-1fb54ca865dd
-- title:
--   numerical Radius adjoint comp comp le: numerical Radius adjoint comp comp le
-- statement:
--   General congruence estimate for numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean#L37-L56
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean#L37-L56

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_Compression
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem numericalRadius_adjoint_comp_comp_le
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) :
    numericalRadius ((V† ∘L A) ∘L V) ≤ ‖V‖ ^ 2 * numericalRadius A := by sorry
