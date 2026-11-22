-- Prove2me | Theorems.Thm_Submodule_exists_generator_of_finrank_eq_one
-- name    : Submodule.exists_generator_of_finrank_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:32.810199+00:00
-- url     : https://prove2.me/theorems/5077abf6-a215-4b1b-83a6-ee8b46a365d2
-- title:
--   Submodule: exists generator of finrank eq one
-- statement:
--   The Submodule construction uses the exists generator of finrank eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L31-L48
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L31-L48

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [Field R]  [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

theorem Submodule.exists_generator_of_finrank_eq_one (p : Submodule R M) (h : Module.finrank R p = 1) :
    ∃ (v : M), v ≠ 0 ∧ Submodule.span R {v} = p := by sorry
