-- Prove2me | solution 1 for P2M_BruhatTits_exists_repr_inv__9cbdeb29df9b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:14:56.171571+00:00
-- url     : https://prove2.me/submissions/6bb6be07-21b4-4119-a22a-3a26afa05692

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
import Theorems.Thm_P2M_BruhatTits_exists_repr_inv__of_fixed_37640b29b3c7

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise
namespace BruhatTits
theorem _root_.solution (M L : Vertices R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      ⟦b.toLattice⟧ = M ∧ ⟦(b.ntwist₂ hϖ (inv M L) 0).toLattice⟧ = L := by
  refine Quotient.inductionOn' M (fun M ↦ ?_)
  obtain ⟨ϖ, hϖ, b, rfl, hL⟩ := exists_repr_inv'_of_fixed M L
  use ϖ, hϖ, b
end BruhatTits
