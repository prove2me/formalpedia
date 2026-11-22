-- Prove2me | Theorems.Thm_valuation_lt_one_of_irreducible
-- name    : valuation_lt_one_of_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:41.231731+00:00
-- url     : https://prove2.me/theorems/591660d6-8678-4c00-b182-ffc0b682cd87
-- title:
--   valuation lt one of irreducible: valuation lt one of irreducible
-- statement:
--   The valuation lt one of irreducible construction uses the valuation lt one of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L123-L129
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L123-L129

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
include hϖ

theorem valuation_lt_one_of_irreducible : v ϖ < 1 := by sorry
