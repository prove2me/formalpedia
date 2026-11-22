-- Prove2me | Theorems.Thm_BruhatTits_isNeighbour_def
-- name    : BruhatTits.isNeighbour_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:48.573748+00:00
-- url     : https://prove2.me/theorems/8a96e7e0-8893-4925-b1cb-b4ac4ba02873
-- title:
--   Bruhat Tits: is Neighbour def
-- statement:
--   The Bruhat Tits construction uses the is Neighbour def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L56-L58
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L56-L58

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

theorem BruhatTits.isNeighbour_def (x y : Vertices R) :
    IsNeighbour x y ↔ inv x y = 1 := by sorry
