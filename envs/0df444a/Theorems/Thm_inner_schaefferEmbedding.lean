-- Prove2me | Theorems.Thm_inner_schaefferEmbedding
-- name    : inner_schaefferEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:17.655642+00:00
-- url     : https://prove2.me/theorems/50fbaeb4-b7e3-5294-af4b-e5548ffabc8d
-- title:
--   inner schaeffer Embedding: inner schaeffer Embedding
-- statement:
--   The coordinate-zero embedding preserves the inner product.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L41-L43
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean#L41-L43

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

theorem inner_schaefferEmbedding (x y : E) :
    ⟪schaefferEmbedding x, schaefferEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by sorry
