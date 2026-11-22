-- Prove2me | solution 1 for cartan_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:31:17.94511+00:00
-- url     : https://prove2.me/submissions/11a41209-110a-4972-a522-c49748e88513

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Theorems.Thm_P2M_cartan_decomposition_unique__6facbe8d407d
import Theorems.Thm_eq_of_twist_eq_of_antitone

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}
theorem _root_.solution {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ hϖ f' * k₂') :
    f = f' := by
  obtain ⟨σ, hσ⟩ := cartan_decomposition_unique' h
  exact (eq_of_twist_eq_of_antitone f' f σ hf' hf hσ.symm).symm
