-- Prove2me | Theorems.Thm_valuation_eq_one_iff
-- name    : valuation_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:16.447724+00:00
-- url     : https://prove2.me/theorems/bbe761f6-fc78-4fe4-8f7b-58f79eaa2319
-- title:
--   valuation eq one iff: valuation eq one iff
-- statement:
--   The valuation eq one iff construction uses the valuation eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L104-L117
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L104-L117

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K

theorem valuation_eq_one_iff (a : R) : IsUnit a ↔ v a = 1 := by sorry
