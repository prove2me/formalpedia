-- Prove2me | Theorems.Thm_inner_schaefferNetworkEmbedding
-- name    : inner_schaefferNetworkEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:23.139109+00:00
-- url     : https://prove2.me/theorems/ad2f8687-aabf-423b-aa9e-100f9dfd766f
-- title:
--   inner schaeffer Network Embedding: inner schaeffer Network Embedding
-- statement:
--   The network embedding preserves inner products.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L166-L169
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L166-L169

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
omit [CompleteSpace E]

theorem inner_schaefferNetworkEmbedding (x y : E) :
    ⟪schaefferNetworkEmbedding x, schaefferNetworkEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by sorry
