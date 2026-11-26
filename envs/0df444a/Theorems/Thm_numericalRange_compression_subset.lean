-- Prove2me | Theorems.Thm_numericalRange_compression_subset
-- name    : numericalRange_compression_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:11.297125+00:00
-- url     : https://prove2.me/theorems/63ee83bf-4542-534c-b423-369b5a9d2356
-- title:
--   numerical Range compression subset: numerical Range compression subset
-- statement:
--   The numerical range of an isometric compression is contained in the
--   original numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean#L21-L34
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean#L21-L34

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

theorem numericalRange_compression_subset
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) (hV : Isometry V) :
    numericalRange ((V† ∘L A) ∘L V) ⊆ numericalRange A := by sorry
