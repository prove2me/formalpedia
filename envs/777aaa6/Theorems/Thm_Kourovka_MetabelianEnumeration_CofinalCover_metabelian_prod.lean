-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_metabelian_prod
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.metabelian_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:02.876863+00:00
-- url     : https://prove2.me/theorems/cb248198-57c9-4d21-94d5-2c3fb07bdf46
-- title:
--   Cofinal Cover: metabelian prod
-- statement:
--   The Cofinal Cover construction uses the metabelian prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L110-L114
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L110-L114

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.metabelian_prod (hG : Metabelian G) (hH : Metabelian H) : Metabelian (G × H) := by sorry
