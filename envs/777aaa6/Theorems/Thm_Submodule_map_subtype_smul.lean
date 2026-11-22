-- Prove2me | Theorems.Thm_Submodule_map_subtype_smul
-- name    : Submodule.map_subtype_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:43:14.973049+00:00
-- url     : https://prove2.me/theorems/4330cbe4-9ade-4459-bfb9-76ad08a0ae95
-- title:
--   Submodule: map subtype smul
-- statement:
--   The Submodule construction uses the map subtype smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L207-L211
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L207-L211

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem Submodule.map_subtype_smul (I : Ideal R) (p : Submodule R M) :
    Submodule.map p.subtype (I • ⊤) = I • p := by sorry
