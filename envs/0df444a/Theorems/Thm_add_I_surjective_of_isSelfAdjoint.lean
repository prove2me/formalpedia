-- Prove2me | Theorems.Thm_add_I_surjective_of_isSelfAdjoint
-- name    : add_I_surjective_of_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:25.499688+00:00
-- url     : https://prove2.me/theorems/7265ecf1-9fd7-58a5-973b-ed7bf07648d0
-- title:
--   add I surjective of is Self Adjoint: add I surjective of is Self Adjoint
-- statement:
--   For a self-adjoint operator, `A + iI` maps its domain onto the ambient space.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L270-L272
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L270-L272

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic
set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem add_I_surjective_of_isSelfAdjoint (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (fun x : A.domain => A x + Complex.I • (x : E)) := by sorry
