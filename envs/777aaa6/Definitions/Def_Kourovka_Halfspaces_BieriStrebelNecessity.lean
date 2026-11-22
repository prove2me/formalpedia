-- Prove2me | Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
-- name    : Kourovka_Halfspaces_BieriStrebelNecessity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:22:49.460312+00:00
-- url     : https://prove2.me/theorems/f4b63c57-3670-4f1a-ba88-f9476aae34b9
-- title:
--   Bieri Strebel Necessity
-- statement:
--   Definitions and structural lemmas for Bieri Strebel Necessity, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
def kernelEquiv {G : Type} [Group G] (e : G ≃* E) (π : E →* Multiplicative L) :
    (π.comp e.toMonoidHom).ker ≃* π.ker where
  toFun n := ⟨e n.val, n.property⟩
  invFun n := ⟨e.symm n.val, by
    change π (e (e.symm n.val)) = 1
    rw [e.apply_symm_apply]
    exact n.property⟩
  left_inv n := Subtype.ext (e.symm_apply_apply n.val)
  right_inv n := Subtype.ext (e.apply_symm_apply n.val)
  map_mul' a b := Subtype.ext (e.map_mul a.val b.val)
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity


