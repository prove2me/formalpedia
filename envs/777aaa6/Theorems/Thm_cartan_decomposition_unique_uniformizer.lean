-- Prove2me | Theorems.Thm_cartan_decomposition_unique_uniformizer
-- name    : cartan_decomposition_unique_uniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:17:28.683579+00:00
-- url     : https://prove2.me/theorems/bcb83313-ad4a-420a-bac4-048b47e99ffd
-- title:
--   cartan decomposition unique uniformizer: cartan decomposition unique uniformizer
-- statement:
--   The Cartan decomposition is unique, independent of the choice of a uniformizer.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L199-L207
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L199-L207

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem cartan_decomposition_unique_uniformizer
    {ϖ ϖ' : R} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ' hϖ' f' * k₂') :
    f = f' := by sorry
