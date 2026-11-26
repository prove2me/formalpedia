-- Prove2me | Theorems.Thm_spectral_theorem_intrinsic
-- name    : spectral_theorem_intrinsic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:41.850165+00:00
-- url     : https://prove2.me/theorems/d970703e-000f-4921-a827-be366bb38434
-- title:
--   spectral theorem intrinsic: spectral theorem intrinsic
-- statement:
--   The unbounded spectral theorem in intrinsic PVM form: every self-adjoint
--   partial operator has a spectral representation, unique on Borel sets.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L164-L173
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L164-L173

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem spectral_theorem_intrinsic
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.Represents A ∧
      ∀ F_pvm : PVM E, F_pvm.Represents A →
        ∀ S : Set ℝ, MeasurableSet S → E_pvm.proj S = F_pvm.proj S := by sorry
