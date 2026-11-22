-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.first_kernel_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:26.820008+00:00
-- url     : https://prove2.me/submissions/fa6572b9-0993-4ae0-8487-4c84a42ab737

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution [IsMulCommutative H] (p : G →* Q) (q : H →* Q) :
    (first p q).ker ≤ Subgroup.center (pullback p q) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · change y.val.1 * x.val.1 = x.val.1 * y.val.1
    have hx' : x.val.1 = 1 := hx
    simp [hx']
  · exact mul_comm _ _
end Kourovka.MetabelianEnumeration.CofinalCover
