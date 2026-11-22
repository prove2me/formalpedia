-- Prove2me | Theorems.Thm_BruhatTits_exists_trafo_to_isStandard
-- name    : BruhatTits.exists_trafo_to_isStandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:40.231167+00:00
-- url     : https://prove2.me/theorems/5384dcd1-05e4-44e9-ac29-0f8a1b7e21c1
-- title:
--   Bruhat Tits: exists trafo to is Standard
-- statement:
--   Any simple chain of lattices can be transformed by an element of `GL₂(K)` to a standard
--   chain, i.e. up to a change of coordinates is every simple chain a standard chain.
--   This is later used to show acyclicity of the Bruhat-Tits graph.
--
--   Prop. 2.1 in Casselman.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L653-L658
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L653-L658

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
open IsLocalRing
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.exists_trafo_to_isStandard (l : List (BruhatTits.Lattice R)) (hl : l.IsSimpleChain) :
    ∃ (g : GL (Fin 2) K), (g • l).IsStandard := by sorry
