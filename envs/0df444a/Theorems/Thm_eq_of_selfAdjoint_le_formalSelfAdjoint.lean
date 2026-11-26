-- Prove2me | Theorems.Thm_eq_of_selfAdjoint_le_formalSelfAdjoint
-- name    : eq_of_selfAdjoint_le_formalSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:51.190547+00:00
-- url     : https://prove2.me/theorems/f0244966-4416-44e6-8ad9-00f439c60f20
-- title:
--   eq of self Adjoint le formal Self Adjoint: eq of self Adjoint le formal Self Adjoint
-- statement:
--   A symmetric extension of a self-adjoint partial linear operator equals that operator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/CayleyCalculus.lean#L261-L273
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/CayleyCalculus.lean#L261-L273

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem eq_of_selfAdjoint_le_formalSelfAdjoint
    (A B : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (hAB : A ≤ B) (hB : B.IsFormalAdjoint B) : B = A := by sorry
