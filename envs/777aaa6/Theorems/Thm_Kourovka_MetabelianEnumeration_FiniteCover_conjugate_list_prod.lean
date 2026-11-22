-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_conjugate_list_prod
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.conjugate_list_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:19.507364+00:00
-- url     : https://prove2.me/theorems/e271e164-9e53-4636-861e-4216872995ae
-- title:
--   Finite Cover: conjugate list prod
-- statement:
--   The Finite Cover construction uses the conjugate list prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L21-L24
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L21-L24

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.conjugate_list_prod (l : List G) (w : G) :
    conjugate l.prod w = (l.map fun x => conjugate x w).prod := by sorry
