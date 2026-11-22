-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_pullback_metabelian
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.pullback_metabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:09:51.979182+00:00
-- url     : https://prove2.me/theorems/f468b3ad-8363-41b7-a20c-0b64815db140
-- title:
--   Cofinal Cover: pullback metabelian
-- statement:
--   The Cofinal Cover construction uses the pullback metabelian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L116-L119
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L116-L119

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.pullback_metabelian [IsMulCommutative H] (p : G →* Q) (q : H →* Q)
    (hG : Metabelian G) : Metabelian (pullback p q) := by sorry
