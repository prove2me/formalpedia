-- Prove2me | Theorems.Thm_BruhatTits_isNeighbour_iff
-- name    : BruhatTits.isNeighbour_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:18.360941+00:00
-- url     : https://prove2.me/theorems/a422b1e1-1115-4618-a8ae-85fdc5ae543d
-- title:
--   Bruhat Tits: is Neighbour iff
-- statement:
--   Two vertices are neighbours if and only if there exist representatives L and M and a uniformizer ϖ
--   such that ϖ • L < M < L, i.e. if `L` is a standard neighbour of `M`.
--
--   This is a common alternative way of defining `BruhatTits.IsNeighbour`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L198-L216
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L198-L216

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

theorem BruhatTits.isNeighbour_iff (L M : Vertices R) :
    IsNeighbour L M ↔ ∃ (ϖ : R) (_ : Irreducible ϖ) (L' M' : BruhatTits.Lattice R),
      ⟦L'⟧ = L ∧ ⟦M'⟧ = M ∧ ϖ • L'.M < M'.M ∧ M'.M < L'.M := by sorry
