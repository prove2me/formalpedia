-- Prove2me | Theorems.Thm_stone_theorem_intrinsic
-- name    : stone_theorem_intrinsic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:42.460775+00:00
-- url     : https://prove2.me/theorems/f65f94a1-77dc-5b1d-8654-82dfba11d433
-- title:
--   stone theorem intrinsic: stone theorem intrinsic
-- statement:
--   Stone's theorem in both directions: strongly continuous one-parameter
--   unitary groups have self-adjoint generators, and every self-adjoint operator
--   generates such a group.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Intrinsic.lean#L41-L53
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Intrinsic.lean#L41-L53

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Stone_Intrinsic
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem stone_theorem_intrinsic :
    (∀ U : StrongContUnitary E, ∃ A : E →ₗ.[ℂ] E,
      IsSelfAdjoint A ∧ U.Generates A) ∧
    (∀ A : E →ₗ.[ℂ] E, IsSelfAdjoint A →
      ∃ U : StrongContUnitary E, U.Generates A) := by sorry
