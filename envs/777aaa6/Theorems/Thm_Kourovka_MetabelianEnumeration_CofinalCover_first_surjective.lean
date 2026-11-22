-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_surjective
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.first_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:22.305001+00:00
-- url     : https://prove2.me/theorems/2ff51017-2cce-4772-aaa8-b33fa797e285
-- title:
--   Cofinal Cover: first surjective
-- statement:
--   The Cofinal Cover construction uses the first surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L44-L48
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L44-L48

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.first_surjective (p : G →* Q) (q : H →* Q) (hq : Function.Surjective q) :
    Function.Surjective (first p q) := by sorry
