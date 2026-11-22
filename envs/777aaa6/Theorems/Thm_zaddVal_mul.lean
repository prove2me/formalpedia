-- Prove2me | Theorems.Thm_zaddVal_mul
-- name    : zaddVal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:43:06.924447+00:00
-- url     : https://prove2.me/theorems/501662d2-22a4-4620-9b33-d2d86c1966aa
-- title:
--   zadd Val mul: zadd Val mul
-- statement:
--   The zadd Val mul construction uses the zadd Val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L322-L332
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L322-L332

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem zaddVal_mul (x y : Kˣ) :
    zaddVal (R := R) (x * y) = zaddVal (R := R) x + zaddVal (R := R) y := by sorry
