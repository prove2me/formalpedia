-- Prove2me | Theorems.Thm_valuation_irreducible_zpow_eq_one_iff
-- name    : valuation_irreducible_zpow_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:34.365479+00:00
-- url     : https://prove2.me/theorems/b6a70e17-bef4-4611-a998-336849081be4
-- title:
--   valuation irreducible zpow eq one iff: valuation irreducible zpow eq one iff
-- statement:
--   The valuation irreducible zpow eq one iff construction uses the valuation irreducible zpow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L202-L209
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L202-L209

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
omit [IsDiscreteValuationRing R]

theorem valuation_irreducible_zpow_eq_one_iff (n : ℤ) : v (ϖ.val ^ n) = 1 ↔ n = 0 := by sorry
