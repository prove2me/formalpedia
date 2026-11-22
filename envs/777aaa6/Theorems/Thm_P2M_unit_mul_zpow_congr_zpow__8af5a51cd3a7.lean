-- Prove2me | Theorems.Thm_P2M_unit_mul_zpow_congr_zpow__8af5a51cd3a7
-- name    : P2M_unit_mul_zpow_congr_zpow__8af5a51cd3a7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:11.52668+00:00
-- url     : https://prove2.me/theorems/0d282396-b82c-4399-b21f-c7ec501805b8
-- title:
--   P2 M unit mul zpow congr zpow  8af5a51cd3a7: P2 M unit mul zpow congr zpow  8af5a51cd3a7
-- statement:
--   The P2 M unit mul zpow congr zpow  8af5a51cd3a7 construction uses the P2 M unit mul zpow congr zpow  8af5a51cd3a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L164-L186
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L164-L186

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

theorem P2M_unit_mul_zpow_congr_zpow__8af5a51cd3a7 (a b : Rˣ) (m n : ℤ) (h : a * ϖ.val ^ m = b * ϖ.val ^ n) :
    m = n := by sorry

alias «unit_mul_zpow_congr_zpow'» := P2M_unit_mul_zpow_congr_zpow__8af5a51cd3a7
