-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.pullback_second_kernel_commutative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:08.612777+00:00
-- url     : https://prove2.me/submissions/4d9c79bc-e98e-4605-820d-628ed768d1ce

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution {Q H : Type} [Group Q] [Group H]
    (p : G →* Q) (q : H →* Q) [IsMulCommutative p.ker] :
    IsMulCommutative (CofinalCover.second p q).ker := by
  let e := CofinalCover.secondKernelEquiv p q
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact mul_comm _ _
end Kourovka.MetabelianEnumeration.CommutatorModule
