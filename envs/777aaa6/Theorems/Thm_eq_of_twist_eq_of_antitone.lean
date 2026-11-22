-- Prove2me | Theorems.Thm_eq_of_twist_eq_of_antitone
-- name    : eq_of_twist_eq_of_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:17:26.54657+00:00
-- url     : https://prove2.me/theorems/5f09c2af-8c55-4345-8702-835c9a74516f
-- title:
--   eq of twist eq of antitone: eq of twist eq of antitone
-- statement:
--   The eq of twist eq of antitone construction uses the eq of twist eq of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L145-L152
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L145-L152

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

theorem eq_of_twist_eq_of_antitone (f g : Fin k → ℤ) (σ : Equiv.Perm (Fin k))
    (hf : Antitone f) (hg : Antitone g) (h : f = g ∘ σ) :
    f = g := by sorry
