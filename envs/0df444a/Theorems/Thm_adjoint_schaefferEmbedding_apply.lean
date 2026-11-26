-- Prove2me | Theorems.Thm_adjoint_schaefferEmbedding_apply
-- name    : adjoint_schaefferEmbedding_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:57.771114+00:00
-- url     : https://prove2.me/theorems/43d9b02a-69eb-52c6-86f2-c0d837a2c8bb
-- title:
--   adjoint schaeffer Embedding apply: adjoint schaeffer Embedding apply
-- statement:
--   The adjoint of the coordinate-zero embedding extracts coordinate zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L46-L50
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L46-L50

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

theorem adjoint_schaefferEmbedding_apply (f : SchaefferSpace E) :
    ContinuousLinearMap.adjoint (schaefferEmbedding : E →L[ℂ] SchaefferSpace E) f = f 0 := by sorry
