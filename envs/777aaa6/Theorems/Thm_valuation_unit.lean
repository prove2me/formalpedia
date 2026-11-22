-- Prove2me | Theorems.Thm_valuation_unit
-- name    : valuation_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:09.856339+00:00
-- url     : https://prove2.me/theorems/1cd992ca-8d82-4ce5-834e-096541c0131b
-- title:
--   valuation unit: valuation unit
-- statement:
--   The valuation unit construction uses the valuation unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L98-L99
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L98-L99

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K

theorem valuation_unit (a : Rˣ) : v a = 1 := by sorry
