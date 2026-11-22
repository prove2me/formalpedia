-- Prove2me | Theorems.Thm_ideal_smul_lt_of_ne_bot
-- name    : ideal_smul_lt_of_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:58.410885+00:00
-- url     : https://prove2.me/theorems/b9a74d46-1b3a-4898-955a-dccd1883898d
-- title:
--   ideal smul lt of ne bot: ideal smul lt of ne bot
-- statement:
--   The ideal smul lt of ne bot construction uses the ideal smul lt of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L213-L235
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L213-L235

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem ideal_smul_lt_of_ne_bot {I : Ideal R} (p : Submodule R M)
    (q : { q : Submodule R p // (I • ⊤ : Submodule R p) ≤ q} ) (h : q ≠ ⊥) :
    I • p < Submodule.map p.subtype q.val := by sorry
