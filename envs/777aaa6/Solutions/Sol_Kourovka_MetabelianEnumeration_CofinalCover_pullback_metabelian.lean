-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.pullback_metabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:19.773956+00:00
-- url     : https://prove2.me/submissions/b3a46e70-c913-47a1-9eab-922d5a5fc620

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_metabelian_of_injective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_metabelian_prod

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution [IsMulCommutative H] (p : G →* Q) (q : H →* Q)
    (hG : Metabelian G) : Metabelian (pullback p q) :=
  metabelian_of_injective (pullback p q).subtype Subtype.val_injective
    (metabelian_prod hG (fun _ _ _ _ => mul_comm _ _))
end Kourovka.MetabelianEnumeration.CofinalCover
