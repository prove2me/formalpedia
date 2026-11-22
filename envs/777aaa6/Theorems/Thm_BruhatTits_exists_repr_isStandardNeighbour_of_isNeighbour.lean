-- Prove2me | Theorems.Thm_BruhatTits_exists_repr_isStandardNeighbour_of_isNeighbour
-- name    : BruhatTits.exists_repr_isStandardNeighbour_of_isNeighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:19.243545+00:00
-- url     : https://prove2.me/theorems/a075a837-f26e-4d9e-9b4f-c50a111dc779
-- title:
--   Bruhat Tits: exists repr is Standard Neighbour of is Neighbour
-- statement:
--   If `M` is a lattice with neighbour `x`, there exists a representative `L` of `x` such that
--   `L` is a standard neighbour of `M`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L186-L190
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L186-L190

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

theorem BruhatTits.exists_repr_isStandardNeighbour_of_isNeighbour (M : BruhatTits.Lattice R) (x : Vertices R)
    (h : IsNeighbour ⟦M⟧ x) :
    ∃ (L : BruhatTits.Lattice R), ⟦L⟧ = x ∧ IsStandardNeighbour L M := by sorry
