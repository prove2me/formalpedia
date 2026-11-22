-- Prove2me | Theorems.Thm_Submodule_comap_subtype_smul
-- name    : Submodule.comap_subtype_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:42:47.696512+00:00
-- url     : https://prove2.me/theorems/c357d431-61fc-4319-bfe5-751c39a3003f
-- title:
--   Submodule: comap subtype smul
-- statement:
--   The Submodule construction uses the comap subtype smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L201-L204
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L201-L204

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem Submodule.comap_subtype_smul (I : Ideal R) (p : Submodule R M) :
    Submodule.comap p.subtype (I • p) = I • ⊤ := by sorry
