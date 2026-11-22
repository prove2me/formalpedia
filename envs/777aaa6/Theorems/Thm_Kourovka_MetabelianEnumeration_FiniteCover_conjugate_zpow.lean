-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_conjugate_zpow
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.conjugate_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:19.015074+00:00
-- url     : https://prove2.me/theorems/42a48145-c47c-415e-89e6-6ed341fba2c0
-- title:
--   Finite Cover: conjugate zpow
-- statement:
--   The Finite Cover construction uses the conjugate zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L26-L29
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L26-L29

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.conjugate_zpow (x w : G) (n : ℤ) :
    conjugate (x ^ n) w = conjugate x w ^ n := by sorry
