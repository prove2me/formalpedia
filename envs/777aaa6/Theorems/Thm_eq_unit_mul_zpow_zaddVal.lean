-- Prove2me | Theorems.Thm_eq_unit_mul_zpow_zaddVal
-- name    : eq_unit_mul_zpow_zaddVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:48.105276+00:00
-- url     : https://prove2.me/theorems/e6074fb9-3dfb-4188-836d-98a7ed7a8e91
-- title:
--   eq unit mul zpow zadd Val: eq unit mul zpow zadd Val
-- statement:
--   The eq unit mul zpow zadd Val construction uses the eq unit mul zpow zadd Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L317-L319
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L317-L319

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ

theorem eq_unit_mul_zpow_zaddVal (x : Kˣ) :
    ∃ (u : Rˣ), u * ϖ.val ^ zaddVal (R := R) x = x := by sorry
