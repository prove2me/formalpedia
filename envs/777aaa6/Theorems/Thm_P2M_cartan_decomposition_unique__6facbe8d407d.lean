-- Prove2me | Theorems.Thm_P2M_cartan_decomposition_unique__6facbe8d407d
-- name    : P2M_cartan_decomposition_unique__6facbe8d407d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:17:22.044775+00:00
-- url     : https://prove2.me/theorems/1188be34-3492-412a-9bee-b613c5a04706
-- title:
--   P2 M cartan decomposition unique  6facbe8d407d: P2 M cartan decomposition unique  6facbe8d407d
-- statement:
--   The P2 M cartan decomposition unique  6facbe8d407d construction uses the P2 M cartan decomposition unique  6facbe8d407d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L127-L143
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L127-L143

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

theorem P2M_cartan_decomposition_unique__6facbe8d407d {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ}
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ hϖ f' * k₂') :
    ∃ σ : Equiv.Perm (Fin k), f ∘ σ = f' := by sorry

alias «cartan_decomposition_unique'» := P2M_cartan_decomposition_unique__6facbe8d407d
