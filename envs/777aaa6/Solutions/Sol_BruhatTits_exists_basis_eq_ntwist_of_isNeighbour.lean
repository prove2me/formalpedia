-- Prove2me | solution 1 for BruhatTits.exists_basis_eq_ntwist_of_isNeighbour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:14:55.655286+00:00
-- url     : https://prove2.me/submissions/34b1ad17-90ea-436a-889f-089a2e592a2d

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_P2M_BruhatTits_exists_repr_inv__of_fixed_37640b29b3c7


set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
variable [IsDiscreteValuationRing R]
variable [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (M : BruhatTits.Lattice R) (L : Vertices R)
    (h : IsNeighbour ⟦M⟧ L) :
    ∃ (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    b.toLattice = M ∧ ⟦(b.ntwist₂ hϖ 1 0).toLattice⟧ = L := by
  classical
  obtain ⟨ϖ, hϖ, b, rfl, h1⟩ := exists_repr_inv'_of_fixed M L
  have : inv _ _ = 1 := h
  rw [this] at h1
  use b, ϖ, hϖ
end BruhatTits
