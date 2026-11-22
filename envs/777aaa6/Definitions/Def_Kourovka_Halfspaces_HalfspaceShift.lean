-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
-- name    : Kourovka_Halfspaces_HalfspaceShift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:21:53.115186+00:00
-- url     : https://prove2.me/theorems/9eb71c88-4714-4a01-b5b2-93a06fa23a23
-- title:
--   Halfspace Shift
-- statement:
--   Definitions and structural lemmas for Halfspace Shift, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
end Kourovka.MetabelianEnumeration.SchreierHeights


