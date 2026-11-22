-- Prove2me | solution 1 for BruhatTits.isNeighbour_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:21:09.398171+00:00
-- url     : https://prove2.me/submissions/424d6e28-7738-490b-bb15-8ec838887164

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_BruhatTits_isNeighbour_symm
import Theorems.Thm_BruhatTits_isNeighbour_of_isStandardNeighbour
import Theorems.Thm_BruhatTits_exists_repr_isStandardNeighbour_of_isNeighbour
import Theorems.Thm_maximalIdeal_smul_eq_uniformizer_smul


set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
variable [IsDiscreteValuationRing R]
variable [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (L M : Vertices R) :
    IsNeighbour L M ↔ ∃ (ϖ : R) (_ : Irreducible ϖ) (L' M' : BruhatTits.Lattice R),
      ⟦L'⟧ = L ∧ ⟦M'⟧ = M ∧ ϖ • L'.M < M'.M ∧ M'.M < L'.M := by
  constructor
  · refine Quotient.inductionOn L (fun L h ↦ ?_)
    obtain ⟨M', hM, hstd⟩ := exists_repr_isStandardNeighbour_of_isNeighbour L M h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    exact ⟨ϖ, hϖ, L, M', rfl, hM, hstd.ϖlt ϖ hϖ, hstd.lt⟩
  · intro ⟨ϖ, hϖ, L', M', hL, hM, hϖlt, hlt⟩
    have hstd : IsStandardNeighbour M' L' := {
      lt := hlt
      ϖlt := by
        intro ϖ' hϖ'
        rw [← maximalIdeal_smul_eq_uniformizer_smul _ hϖ',
          maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
        exact hϖlt
    }
    rw [← hL, ← hM, isNeighbour_symm]
    exact isNeighbour_of_isStandardNeighbour hstd
end BruhatTits
