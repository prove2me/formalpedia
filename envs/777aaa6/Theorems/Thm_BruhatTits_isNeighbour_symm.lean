-- Prove2me | Theorems.Thm_BruhatTits_isNeighbour_symm
-- name    : BruhatTits.isNeighbour_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:32.240347+00:00
-- url     : https://prove2.me/theorems/954f66c0-2fa4-4370-9baf-b239b4d4300c
-- title:
--   Bruhat Tits: is Neighbour symm
-- statement:
--   The Bruhat Tits construction uses the is Neighbour symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L75-L78
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L75-L78

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
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isNeighbour_symm (x y : Vertices R) :
    IsNeighbour x y ↔ IsNeighbour y x := by sorry
