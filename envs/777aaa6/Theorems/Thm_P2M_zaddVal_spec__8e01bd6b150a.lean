-- Prove2me | Theorems.Thm_P2M_zaddVal_spec__8e01bd6b150a
-- name    : P2M_zaddVal_spec__8e01bd6b150a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:03.961231+00:00
-- url     : https://prove2.me/theorems/680c4094-2ac1-4bca-b6ce-c5b379d1b548
-- title:
--   P2 M zadd Val spec  8e01bd6b150a: P2 M zadd Val spec  8e01bd6b150a
-- statement:
--   The P2 M zadd Val spec  8e01bd6b150a construction uses the P2 M zadd Val spec  8e01bd6b150a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L147-L151
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L147-L151

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem P2M_zaddVal_spec__8e01bd6b150a (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    zaddVal (R := R) x = zaddVal' ϖ hϖ x := by sorry

alias «zaddVal_spec'» := P2M_zaddVal_spec__8e01bd6b150a
