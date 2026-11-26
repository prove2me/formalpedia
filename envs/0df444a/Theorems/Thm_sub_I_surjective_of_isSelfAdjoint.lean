-- Prove2me | Theorems.Thm_sub_I_surjective_of_isSelfAdjoint
-- name    : sub_I_surjective_of_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:27.02325+00:00
-- url     : https://prove2.me/theorems/8b57fdb0-eb32-5a15-8c69-b10e422f2cf4
-- title:
--   sub I surjective of is Self Adjoint: sub I surjective of is Self Adjoint
-- statement:
--   For a self-adjoint operator, `A - iI` maps its domain onto the ambient space.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L275-L277
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L275-L277

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic
set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem sub_I_surjective_of_isSelfAdjoint (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (fun x : A.domain => A x - Complex.I • (x : E)) := by sorry
