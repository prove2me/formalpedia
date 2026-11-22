-- Prove2me | Theorems.Thm_zaddVal_eq_iff
-- name    : zaddVal_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:14.676907+00:00
-- url     : https://prove2.me/theorems/c5384ad8-5967-4e80-99c7-6711ecf78c33
-- title:
--   zadd Val eq iff: zadd Val eq iff
-- statement:
--   The zadd Val eq iff construction uses the zadd Val eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L289-L308
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L289-L308

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem zaddVal_eq_iff (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by sorry
