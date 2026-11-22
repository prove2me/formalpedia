-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_kernel_central
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.first_kernel_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:03.793359+00:00
-- url     : https://prove2.me/theorems/e99934b1-df74-41cb-9df9-0b9207e4fd34
-- title:
--   Cofinal Cover: first kernel central
-- statement:
--   The Cofinal Cover construction uses the first kernel central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L92-L102
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean#L92-L102

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]

theorem Kourovka.MetabelianEnumeration.CofinalCover.first_kernel_central [IsMulCommutative H] (p : G →* Q) (q : H →* Q) :
    (first p q).ker ≤ Subgroup.center (pullback p q) := by sorry
