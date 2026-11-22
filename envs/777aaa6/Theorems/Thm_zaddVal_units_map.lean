-- Prove2me | Theorems.Thm_zaddVal_units_map
-- name    : zaddVal_units_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:43:39.022176+00:00
-- url     : https://prove2.me/theorems/e395e9d3-efa4-4815-a6e0-8757bc104f45
-- title:
--   zadd Val units map: zadd Val units map
-- statement:
--   The zadd Val units map construction uses the zadd Val units map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L335-L340
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L335-L340

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem zaddVal_units_map (x : Rˣ) :
    zaddVal (R := R) (Units.map R.subtype x) = 0 := by sorry
