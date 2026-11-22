-- Prove2me | Theorems.Thm_BruhatTits_smul_isChain
-- name    : BruhatTits.smul_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:11.924002+00:00
-- url     : https://prove2.me/theorems/adcc0ae4-c885-4f96-9e65-c9879ac762bc
-- title:
--   Bruhat Tits: smul is Chain
-- statement:
--   `GL₂(K)` preserves `IsSimpleChain`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L316-L330
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L316-L330

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
set_option synthInstance.maxHeartbeats 30000

theorem BruhatTits.smul_isChain (g : GL (Fin 2) K) {l : List (BruhatTits.Lattice R)} (hl : l.IsSimpleChain) :
    (g • l).IsSimpleChain := by sorry
