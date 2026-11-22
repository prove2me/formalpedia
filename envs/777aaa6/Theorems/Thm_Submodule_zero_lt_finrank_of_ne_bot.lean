-- Prove2me | Theorems.Thm_Submodule_zero_lt_finrank_of_ne_bot
-- name    : Submodule.zero_lt_finrank_of_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:43:15.692174+00:00
-- url     : https://prove2.me/theorems/30433516-97ee-405b-8db2-8331dc8f66d0
-- title:
--   Submodule: zero lt finrank of ne bot
-- statement:
--   The Submodule construction uses the zero lt finrank of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L14-L18
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L14-L18

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [Field R]  [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

theorem Submodule.zero_lt_finrank_of_ne_bot (p : Submodule R M) (hp : p ≠ ⊥) :
    0 < Module.finrank R p := by sorry
