-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_second_surjective
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.second_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:58.15846+00:00
-- url     : https://prove2.me/theorems/4a610a3b-2e45-41e5-bd40-9bc7fbda2801
-- title:
--   Cofinal Cover: second surjective
-- statement:
--   The Cofinal Cover construction uses the second surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L50-L54
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L50-L54

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.second_surjective (p : G →* Q) (q : H →* Q) (hp : Function.Surjective p) :
    Function.Surjective (second p q) := by sorry
