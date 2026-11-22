-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_metabelian_of_injective
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.metabelian_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:24.161885+00:00
-- url     : https://prove2.me/theorems/bd08e442-6fe2-4d21-96f3-61e1f2bb19b2
-- title:
--   Cofinal Cover: metabelian of injective
-- statement:
--   The Cofinal Cover construction uses the metabelian of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L104-L108
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L104-L108

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.metabelian_of_injective {E : Type} [Group E] (f : E →* G)
    (hf : Function.Injective f) (hG : Metabelian G) : Metabelian E := by sorry
