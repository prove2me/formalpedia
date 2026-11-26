-- Prove2me | Theorems.Thm_adjoint_schaefferNetworkEmbedding_apply
-- name    : adjoint_schaefferNetworkEmbedding_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:01.461369+00:00
-- url     : https://prove2.me/theorems/d8424905-6228-4005-a189-8b432da9d5d8
-- title:
--   adjoint schaeffer Network Embedding apply: adjoint schaeffer Network Embedding apply
-- statement:
--   The adjoint of the network embedding extracts the system component at site zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L172-L179
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L172-L179

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

theorem adjoint_schaefferNetworkEmbedding_apply (f : SchaefferNetworkSpace E) :
    ContinuousLinearMap.adjoint
      (schaefferNetworkEmbedding : E →L[ℂ] SchaefferNetworkSpace E) f = (f 0).fst := by sorry
