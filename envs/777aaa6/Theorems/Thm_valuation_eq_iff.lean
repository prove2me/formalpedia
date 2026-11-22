-- Prove2me | Theorems.Thm_valuation_eq_iff
-- name    : valuation_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:11.799167+00:00
-- url     : https://prove2.me/theorems/93461bbd-99e9-4819-91b2-83ea4cdda2e5
-- title:
--   valuation eq iff: valuation eq iff
-- statement:
--   The valuation eq iff construction uses the valuation eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L94-L96
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L94-L96

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K

theorem valuation_eq_iff (x y : K) :
    v x = v y ↔ ∃ (a : Rˣ), a * y = x := by sorry
