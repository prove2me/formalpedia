-- Prove2me | solution 1 for BruhatTits.exists_repr_isStandardNeighbour_of_isNeighbour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:19:18.978342+00:00
-- url     : https://prove2.me/submissions/954359ff-0609-491b-adbc-05c9ead15bdd

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_BruhatTits_ntwist_isStandardNeighbour
import Theorems.Thm_BruhatTits_exists_basis_eq_ntwist_of_isNeighbour

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
variable [IsDiscreteValuationRing R]
variable [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (M : BruhatTits.Lattice R) (x : Vertices R)
    (h : IsNeighbour ⟦M⟧ x) :
    ∃ (L : BruhatTits.Lattice R), ⟦L⟧ = x ∧ IsStandardNeighbour L M := by
  obtain ⟨b, ϖ, hϖ, rfl, h1⟩ := exists_basis_eq_ntwist_of_isNeighbour M x h
  refine ⟨(b.ntwist₂ hϖ 1 0).toLattice (R := R), h1, ntwist_isStandardNeighbour b hϖ⟩
end BruhatTits
