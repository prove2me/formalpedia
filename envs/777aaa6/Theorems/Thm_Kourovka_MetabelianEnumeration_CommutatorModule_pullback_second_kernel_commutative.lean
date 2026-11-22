-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_pullback_second_kernel_commutative
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.pullback_second_kernel_commutative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:34.317495+00:00
-- url     : https://prove2.me/theorems/aac79e76-af0c-4039-8fef-2b53b801d068
-- title:
--   Commutator Module: pullback second kernel commutative
-- statement:
--   The Commutator Module construction uses the pullback second kernel commutative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L77-L83
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L77-L83

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]

theorem Kourovka.MetabelianEnumeration.CommutatorModule.pullback_second_kernel_commutative {Q H : Type} [Group Q] [Group H]
    (p : G →* Q) (q : H →* Q) [IsMulCommutative p.ker] :
    IsMulCommutative (CofinalCover.second p q).ker := by sorry
