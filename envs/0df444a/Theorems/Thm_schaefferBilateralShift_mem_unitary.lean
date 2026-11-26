-- Prove2me | Theorems.Thm_schaefferBilateralShift_mem_unitary
-- name    : schaefferBilateralShift_mem_unitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:18.432797+00:00
-- url     : https://prove2.me/theorems/6b56eec7-d9fe-4a4e-b186-76a11a113f6d
-- title:
--   schaeffer Bilateral Shift mem unitary: schaeffer Bilateral Shift mem unitary
-- statement:
--   The bilateral shift is unitary.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L125-L128
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L125-L128

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Operator_Dilation_Halmos
import Definitions.Def_Operator_Dilation_Schaeffer
set_option autoImplicit false
open scoped ENNReal InnerProductSpace
universe u
noncomputable section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem schaefferBilateralShift_mem_unitary :
    schaefferBilateralShift (E := E) ∈
      unitary (SchaefferSpace E →L[ℂ] SchaefferSpace E) := by sorry
