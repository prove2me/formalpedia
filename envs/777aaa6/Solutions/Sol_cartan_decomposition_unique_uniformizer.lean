-- Prove2me | solution 1 for cartan_decomposition_unique_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:32:46.177534+00:00
-- url     : https://prove2.me/submissions/801afbe3-001b-4db2-b6f8-157b2beb41de

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Theorems.Thm_cartanDiag_map_mul
import Theorems.Thm_cartan_decomposition_unique
import Theorems.Thm_GL_map_mul


set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
theorem _root_.solution
    {ϖ ϖ' : R} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ' hϖ' f' * k₂') :
    f = f' := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hϖ'
  rw [cartanDiag_map_mul hϖ hϖ', ← mul_assoc, ← GL.map_mul] at h
  exact cartan_decomposition_unique hf hf' h
