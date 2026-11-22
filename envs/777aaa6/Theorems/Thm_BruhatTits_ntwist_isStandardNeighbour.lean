-- Prove2me | Theorems.Thm_BruhatTits_ntwist_isStandardNeighbour
-- name    : BruhatTits.ntwist_isStandardNeighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:13.144029+00:00
-- url     : https://prove2.me/theorems/e1a96854-274a-47ef-b598-ddc344be520f
-- title:
--   Bruhat Tits: ntwist is Standard Neighbour
-- statement:
--   If `b = (b₁, b₂)` is a basis of `Fin 2 → K`, the span of `(ϖ • b₁, b₂)` is a standard neighbour
--   of the span of `b`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L103-L129
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L103-L129

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

theorem BruhatTits.ntwist_isStandardNeighbour (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    IsStandardNeighbour (b.ntwist₂ hϖ 1 0).toLattice (b.toLattice (R := R)) := by sorry
