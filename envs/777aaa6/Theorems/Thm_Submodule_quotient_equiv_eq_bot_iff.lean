-- Prove2me | Theorems.Thm_Submodule_quotient_equiv_eq_bot_iff
-- name    : Submodule.quotient_equiv_eq_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:07.375621+00:00
-- url     : https://prove2.me/theorems/bbc08493-79af-4fbc-8527-85d8a8d69139
-- title:
--   Submodule: quotient equiv eq bot iff
-- statement:
--   The Submodule construction uses the quotient equiv eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L172-L176
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L172-L176

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem Submodule.quotient_equiv_eq_bot_iff (p : Submodule R M)
    (p' : { p' : Submodule R M // p ≤ p' }) :
    p' = ⊥ ↔ p'.val = p := by sorry
