-- Prove2me | Theorems.Thm_P2M_cartan_decomposition_unique__aux_3e99e4a3d7c4
-- name    : P2M_cartan_decomposition_unique__aux_3e99e4a3d7c4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:17:20.868547+00:00
-- url     : https://prove2.me/theorems/ff27def5-81ea-4529-b416-ef9939e1dd8b
-- title:
--   P2 M cartan decomposition unique  aux 3e99e4a3d7c4: P2 M cartan decomposition unique  aux 3e99e4a3d7c4
-- statement:
--   The P2 M cartan decomposition unique  aux 3e99e4a3d7c4 construction uses the P2 M cartan decomposition unique  aux 3e99e4a3d7c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L56-L125
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L56-L125

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

theorem P2M_cartan_decomposition_unique__aux_3e99e4a3d7c4 (x a : GL (Fin k) R) (f f' : Fin k → ℤ)
    (hax : cartanDiag ϖ hϖ f * a * (cartanDiag ϖ hϖ f')⁻¹ = x) :
    ∃ σ : Equiv.Perm (Fin k), f ∘ σ = f' := by sorry

alias «cartan_decomposition_unique'_aux» := P2M_cartan_decomposition_unique__aux_3e99e4a3d7c4
