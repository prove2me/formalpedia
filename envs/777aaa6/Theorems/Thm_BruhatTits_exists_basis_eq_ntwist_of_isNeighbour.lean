-- Prove2me | Theorems.Thm_BruhatTits_exists_basis_eq_ntwist_of_isNeighbour
-- name    : BruhatTits.exists_basis_eq_ntwist_of_isNeighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:05.147694+00:00
-- url     : https://prove2.me/theorems/749ecf22-7ed4-44c8-934b-23397cfee791
-- title:
--   Bruhat Tits: exists basis eq ntwist of is Neighbour
-- statement:
--   The Bruhat Tits construction uses the exists basis eq ntwist of is Neighbour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L174-L182
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L174-L182

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
variable [IsDiscreteValuationRing R]
variable [IsFractionRing R K]

theorem BruhatTits.exists_basis_eq_ntwist_of_isNeighbour (M : BruhatTits.Lattice R) (L : Vertices R)
    (h : IsNeighbour ⟦M⟧ L) :
    ∃ (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    b.toLattice = M ∧ ⟦(b.ntwist₂ hϖ 1 0).toLattice⟧ = L := by sorry
