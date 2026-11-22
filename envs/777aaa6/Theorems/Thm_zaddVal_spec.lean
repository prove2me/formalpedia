-- Prove2me | Theorems.Thm_zaddVal_spec
-- name    : zaddVal_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:46:55.255176+00:00
-- url     : https://prove2.me/theorems/b107c45f-bcaf-453a-844d-70ba87291b0a
-- title:
--   zadd Val spec: zadd Val spec
-- statement:
--   The zadd Val spec construction uses the zadd Val spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L153-L161
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L153-L161

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem zaddVal_spec (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ)
    (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal (R := R) x) := by sorry
