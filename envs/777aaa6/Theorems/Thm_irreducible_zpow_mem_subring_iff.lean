-- Prove2me | Theorems.Thm_irreducible_zpow_mem_subring_iff
-- name    : irreducible_zpow_mem_subring_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:10.322176+00:00
-- url     : https://prove2.me/theorems/9e199928-4e18-4bde-8a4d-91d162326b1a
-- title:
--   irreducible zpow mem subring iff: irreducible zpow mem subring iff
-- statement:
--   The irreducible zpow mem subring iff construction uses the irreducible zpow mem subring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L257-L270
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L257-L270

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
include hϖ

theorem irreducible_zpow_mem_subring_iff (n : ℤ) : ϖ.val ^ n ∈ R ↔ n ≥ 0 := by sorry
