-- Prove2me | Theorems.Thm_lt_of_ne_top
-- name    : lt_of_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:55.293549+00:00
-- url     : https://prove2.me/theorems/5948a86e-c23f-40a0-b3ed-55c05c0087b3
-- title:
--   lt of ne top: lt of ne top
-- statement:
--   The lt of ne top construction uses the lt of ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L178-L192
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L178-L192

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem lt_of_ne_top (p : Submodule R M) {p' : Submodule R p}
    (q : { q : Submodule R p // p' ≤ q} )
    (h : q ≠ ⊤) : Submodule.map p.subtype q.val < p := by sorry
