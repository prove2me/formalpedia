-- Prove2me | Theorems.Thm_BruhatTits_isNeighbour_of_isStandardNeighbour
-- name    : BruhatTits.isNeighbour_of_isStandardNeighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:20.187964+00:00
-- url     : https://prove2.me/theorems/06318add-0339-4dc7-b7d4-caea39361500
-- title:
--   Bruhat Tits: is Neighbour of is Standard Neighbour
-- statement:
--   If `M` is a standard neighbour of `L`, the vertices `⟦M⟧` and `⟦L⟧` are neighbours.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L134-L172
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L134-L172

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

theorem BruhatTits.isNeighbour_of_isStandardNeighbour {M L : BruhatTits.Lattice R} (h : IsStandardNeighbour M L) :
    IsNeighbour ⟦M⟧ ⟦L⟧ := by sorry
