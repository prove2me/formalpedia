-- Prove2me | solution 1 for BruhatTits.Lattice.mapIntermediate_finrank_eq_one_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:07:33.424176+00:00
-- url     : https://prove2.me/submissions/1e3ac88b-1c5c-4962-82ab-e9c6956d4f92

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
import Theorems.Thm_BruhatTits_Lattice_mapIntermediate_ne_bot_of
import Theorems.Thm_BruhatTits_Lattice_mapIntermediate_ne_top_of
import Theorems.Thm_Submodule_finrank_lt_finrank_of_ne_top
import Theorems.Thm_Submodule_zero_lt_finrank_of_ne_bot


set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
open BruhatTits
set_option synthInstance.maxHeartbeats 30000
open IsLocalRing
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000
open Pointwise
variable [IsFractionRing R K]
namespace BruhatTits
namespace Lattice
theorem _root_.solution {L M : BruhatTits.Lattice R} {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < L.M)
    (h2 : ϖ • L.M < M.M) :
    Module.finrank (ResidueField R) (L.mapIntermediate M) = 1 := by
  have hM'_ne_bot : L.mapIntermediate M ≠ ⊥ := by
    apply Lattice.mapIntermediate_ne_bot_of _ _ hϖ
    · apply le_of_lt
      exact h1
    · exact h2
  have hM'_ne_top : L.mapIntermediate M ≠ ⊤ := by
    apply Lattice.mapIntermediate_ne_top_of _ _ hϖ
    · exact h1
    · apply le_of_lt
      exact h2
  have h1' : Module.finrank (ResidueField R) (L.mapIntermediate M) < 2 := by
    rw [← L.quotient_finrank]
    apply Submodule.finrank_lt_finrank_of_ne_top
    exact hM'_ne_top
  have h2' : 0 < Module.finrank (ResidueField R) (L.mapIntermediate M) := by
    apply Submodule.zero_lt_finrank_of_ne_bot
    exact hM'_ne_bot
  omega
end Lattice
end BruhatTits
