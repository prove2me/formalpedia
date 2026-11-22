-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_abelian_pullback_kernel_finite_generators
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.abelian_pullback_kernel_finite_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:10:44.217397+00:00
-- url     : https://prove2.me/theorems/f38ff0ab-eb1c-4968-8469-3c93afe71cda
-- title:
--   Commutator Module: abelian pullback kernel finite generators
-- statement:
--   The Commutator Module construction uses the abelian pullback kernel finite generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L85-L100
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L85-L100

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]

theorem Kourovka.MetabelianEnumeration.CommutatorModule.abelian_pullback_kernel_finite_generators {α : Type} [Fintype α]
    (R : List (FreeGroup α)) :
    ∃ s : Finset (CofinalCover.second Abelianization.of
      (CofinalCover.abelianQuotientMap R)).ker,
      Subgroup.normalClosure (Subtype.val '' (s : Set (CofinalCover.second Abelianization.of
        (CofinalCover.abelianQuotientMap R)).ker)) =
        (CofinalCover.second Abelianization.of (CofinalCover.abelianQuotientMap R)).ker := by sorry
