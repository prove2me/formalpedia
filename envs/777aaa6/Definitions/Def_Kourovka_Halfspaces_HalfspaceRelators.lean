-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
-- name    : Kourovka_Halfspaces_HalfspaceRelators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:18:51.711262+00:00
-- url     : https://prove2.me/theorems/c52c1d0b-959f-450e-bcda-5a9412792b5d
-- title:
--   Halfspace Relators
-- statement:
--   Definitions and structural lemmas for Halfspace Relators, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceRelators.lean

import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Definitions.Def_Kourovka_Schreier_KernelPresentation
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]
end Kourovka.MetabelianEnumeration.SchreierHeights


