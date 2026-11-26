-- Prove2me | Theorems.Thm_numericalRadius_compression_le
-- name    : numericalRadius_compression_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:14:43.949839+00:00
-- url     : https://prove2.me/theorems/c796f63c-b42f-4688-a913-22282f22c2ea
-- title:
--   numerical Radius compression le: numerical Radius compression le
-- statement:
--   Numerical radius cannot increase under isometric compression.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean#L59-L65
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean#L59-L65

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

theorem numericalRadius_compression_le
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) (hV : Isometry V) :
    numericalRadius ((V† ∘L A) ∘L V) ≤ numericalRadius A := by sorry
