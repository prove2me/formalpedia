-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
-- name    : Kourovka_Halfspaces_HalfspaceGeneration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:21:16.291631+00:00
-- url     : https://prove2.me/theorems/af82cd32-e960-41aa-919c-4bcf4ce9e2ba
-- title:
--   Halfspace Generation
-- statement:
--   Definitions and structural lemmas for Halfspace Generation, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeneration.lean

import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceSplitting HalfspaceLoops
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
end Kourovka.MetabelianEnumeration.SchreierHeights


