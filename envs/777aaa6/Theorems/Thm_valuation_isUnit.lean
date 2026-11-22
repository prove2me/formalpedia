-- Prove2me | Theorems.Thm_valuation_isUnit
-- name    : valuation_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:46:06.896188+00:00
-- url     : https://prove2.me/theorems/4543a78d-f289-4475-9617-fe9f0844e252
-- title:
--   valuation is Unit: valuation is Unit
-- statement:
--   The valuation is Unit construction uses the valuation is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L101-L102
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L101-L102

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K

theorem valuation_isUnit (a : R) (ha : IsUnit a) : v a = 1 := by sorry
