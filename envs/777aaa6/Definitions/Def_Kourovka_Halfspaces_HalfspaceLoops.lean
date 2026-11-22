-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
-- name    : Kourovka_Halfspaces_HalfspaceLoops
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:47:57.846096+00:00
-- url     : https://prove2.me/theorems/3947316a-64c5-4b55-8b36-80bf88f10907
-- title:
--   Halfspace Loops
-- statement:
--   Definitions and structural lemmas for Halfspace Loops, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoops.lean

import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Definitions.Def_Kourovka_Modules_LaurentAction
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
def loopSet (π : E →* Multiplicative L) (χ : L →+ ℝ) (g : X → E)
    (P : ℝ → Prop) : Set π.ker :=
  {n | ∃ w : List (X × Bool), FreeGroup.lift g (FreeGroup.mk w) = n.val ∧
    PathIn (letterHeight (fun x => χ (π (g x)).toAdd)) P 0 w}
end Kourovka.MetabelianEnumeration.HalfspaceLoops


