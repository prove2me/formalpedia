-- Prove2me | Theorems.Thm_P2M_zaddVal__eq_iff_327e0f40dafd
-- name    : P2M_zaddVal__eq_iff_327e0f40dafd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:56:04.075784+00:00
-- url     : https://prove2.me/theorems/9d947a74-3327-4e4e-bbe5-9a3850bd8b04
-- title:
--   P2 M zadd Val  eq iff 327e0f40dafd: P2 M zadd Val  eq iff 327e0f40dafd
-- statement:
--   The P2 M zadd Val  eq iff 327e0f40dafd construction uses the P2 M zadd Val  eq iff 327e0f40dafd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L272-L287
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L272-L287

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem P2M_zaddVal__eq_iff_327e0f40dafd (n : ℤ) (x : Kˣ) :
    zaddVal' (R := R) ϖ hϖ x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by sorry

alias «zaddVal'_eq_iff» := P2M_zaddVal__eq_iff_327e0f40dafd
