-- Prove2me | Theorems.Thm_BruhatTits_smul_isSimilar_iff
-- name    : BruhatTits.smul_isSimilar_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:28.327223+00:00
-- url     : https://prove2.me/theorems/8c739dc6-7684-4862-86b8-165564862888
-- title:
--   Bruhat Tits: smul is Similar iff
-- statement:
--   `GL₂(K)` preserves `IsSimilar`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L291-L313
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L291-L313

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

theorem BruhatTits.smul_isSimilar_iff (g : GL (Fin 2) K) (M L : BruhatTits.Lattice R) :
    Lattice.IsSimilar R (g • M) (g • L) ↔ Lattice.IsSimilar R M L := by sorry
