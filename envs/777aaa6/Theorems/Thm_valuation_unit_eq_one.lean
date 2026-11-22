-- Prove2me | Theorems.Thm_valuation_unit_eq_one
-- name    : valuation_unit_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:46:29.738523+00:00
-- url     : https://prove2.me/theorems/f769613b-4881-4cc7-ba53-5443cba9a55a
-- title:
--   valuation unit eq one: valuation unit eq one
-- statement:
--   The valuation unit eq one construction uses the valuation unit eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L119-L120
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L119-L120

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K

theorem valuation_unit_eq_one (x : Rˣ) : v x = 1 := by sorry
