-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_of
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.abelianQuotientMap_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:08.715662+00:00
-- url     : https://prove2.me/theorems/3db6fa9a-74db-45e8-9c70-fcf4b97a754b
-- title:
--   Cofinal Cover: abelian Quotient Map of
-- statement:
--   The Cofinal Cover construction uses the abelian Quotient Map of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L128-L135
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L128-L135

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.abelianQuotientMap_of {α : Type} (R : List (FreeGroup α)) (a : α) :
    abelianQuotientMap R (Multiplicative.ofAdd (FreeAbelianGroup.of a)) =
      Abelianization.of (PresentedGroup.of a) := by sorry
