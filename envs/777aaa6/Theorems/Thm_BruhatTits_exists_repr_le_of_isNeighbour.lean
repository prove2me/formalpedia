-- Prove2me | Theorems.Thm_BruhatTits_exists_repr_le_of_isNeighbour
-- name    : BruhatTits.exists_repr_le_of_isNeighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:27.008605+00:00
-- url     : https://prove2.me/theorems/9e1a55cf-9721-4d14-8c70-29d5898aa836
-- title:
--   Bruhat Tits: exists repr le of is Neighbour
-- statement:
--   If `M` is a lattice and `x` a neighbour of `⟦M⟧`, there exists a representative
--   `L` of `x` such that `L ≤ M` and `dist M L = 1`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L62-L73
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L62-L73

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

theorem BruhatTits.exists_repr_le_of_isNeighbour (M : BruhatTits.Lattice R) (x : Vertices R)
    (h : IsNeighbour ⟦M⟧ x) :
    ∃ (L : BruhatTits.Lattice R), ⟦L⟧ = x ∧ L.M ≤ M.M ∧ dist M L = 1 := by sorry
