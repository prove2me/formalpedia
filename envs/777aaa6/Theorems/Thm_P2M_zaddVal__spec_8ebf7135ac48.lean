-- Prove2me | Theorems.Thm_P2M_zaddVal__spec_8ebf7135ac48
-- name    : P2M_zaddVal__spec_8ebf7135ac48
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:00.023359+00:00
-- url     : https://prove2.me/theorems/d0a862f6-e139-46ed-91db-c6a08b143c8a
-- title:
--   P2 M zadd Val  spec 8ebf7135ac48: P2 M zadd Val  spec 8ebf7135ac48
-- statement:
--   The P2 M zadd Val  spec 8ebf7135ac48 construction uses the P2 M zadd Val  spec 8ebf7135ac48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L142-L145
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L142-L145

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem P2M_zaddVal__spec_8ebf7135ac48 (x : Kˣ) : ∃ (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal' ϖ hϖ x) := by sorry

alias «zaddVal'_spec» := P2M_zaddVal__spec_8ebf7135ac48
