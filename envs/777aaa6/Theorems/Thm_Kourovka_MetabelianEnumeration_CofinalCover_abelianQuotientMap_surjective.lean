-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_surjective
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.abelianQuotientMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:07.412906+00:00
-- url     : https://prove2.me/theorems/d1004cfe-2cca-409e-a40b-158ddc20737f
-- title:
--   Cofinal Cover: abelian Quotient Map surjective
-- statement:
--   The Cofinal Cover construction uses the abelian Quotient Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L137-L145
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L137-L145

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.abelianQuotientMap_surjective {α : Type} (R : List (FreeGroup α)) :
    Function.Surjective (abelianQuotientMap R) := by sorry
