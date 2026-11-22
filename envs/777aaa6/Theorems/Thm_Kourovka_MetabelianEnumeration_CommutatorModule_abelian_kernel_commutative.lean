-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_abelian_kernel_commutative
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.abelian_kernel_commutative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:25.899484+00:00
-- url     : https://prove2.me/theorems/d775bca6-0ea5-4b29-aa2e-527376c6b68c
-- title:
--   Commutator Module: abelian kernel commutative
-- statement:
--   The Commutator Module construction uses the abelian kernel commutative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L64-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L64-L75

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]

theorem Kourovka.MetabelianEnumeration.CommutatorModule.abelian_kernel_commutative (hG : Metabelian G) :
    IsMulCommutative (Abelianization.of (G := G)).ker := by sorry
