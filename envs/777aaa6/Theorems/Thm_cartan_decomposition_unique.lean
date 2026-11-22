-- Prove2me | Theorems.Thm_cartan_decomposition_unique
-- name    : cartan_decomposition_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:13:55.164806+00:00
-- url     : https://prove2.me/theorems/4867e5b9-3dbe-4fb7-a28b-b53d13487865
-- title:
--   cartan decomposition unique: cartan decomposition unique
-- statement:
--   The cartan decomposition is unique.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L155-L160
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L155-L160

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}

theorem cartan_decomposition_unique {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ hϖ f' * k₂') :
    f = f' := by sorry
