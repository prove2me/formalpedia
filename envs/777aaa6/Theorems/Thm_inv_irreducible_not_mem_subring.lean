-- Prove2me | Theorems.Thm_inv_irreducible_not_mem_subring
-- name    : inv_irreducible_not_mem_subring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:46:55.082714+00:00
-- url     : https://prove2.me/theorems/c514086e-c8cd-4bd6-8600-dcfc995dd36a
-- title:
--   inv irreducible not mem subring: inv irreducible not mem subring
-- statement:
--   The inv irreducible not mem subring construction uses the inv irreducible not mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L213-L226
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L213-L226

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
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]

theorem inv_irreducible_not_mem_subring : ϖ.val⁻¹ ∉ R := by sorry
