-- Prove2me | Theorems.Thm_Submodule_finrank_lt_finrank_of_ne_top
-- name    : Submodule.finrank_lt_finrank_of_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:28.682468+00:00
-- url     : https://prove2.me/theorems/12a0980b-a32e-44bb-80e1-aa379bcf45e9
-- title:
--   Submodule: finrank lt finrank of ne top
-- statement:
--   The Submodule construction uses the finrank lt finrank of ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L20-L29
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L20-L29

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [Field R]  [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

theorem Submodule.finrank_lt_finrank_of_ne_top (p : Submodule R M) (hp : p ≠ ⊤) :
    Module.finrank R p < Module.finrank R M := by sorry
