-- Prove2me | Theorems.Thm_BruhatTits_smul_isStandardNeighbour
-- name    : BruhatTits.smul_isStandardNeighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:22.370374+00:00
-- url     : https://prove2.me/theorems/8b00fa39-596f-473d-8d23-1bdb3ad9e621
-- title:
--   Bruhat Tits: smul is Standard Neighbour
-- statement:
--   `GL₂(K)` preserves `IsStandardNeighbour`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L90-L97
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L90-L97

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

theorem BruhatTits.smul_isStandardNeighbour (g : GL (Fin 2) K) (M L : BruhatTits.Lattice R) (h : IsStandardNeighbour M L) :
    IsStandardNeighbour (g • M) (g • L) := by sorry
