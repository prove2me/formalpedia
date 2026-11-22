-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_commute_hom_of_generators
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.commute_hom_of_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:27.035086+00:00
-- url     : https://prove2.me/theorems/73261995-1623-42f0-b08c-bcc083df339d
-- title:
--   Finite Cover: commute hom of generators
-- statement:
--   Commutativity of the images of generators extends to the whole group.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L130-L154
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L130-L154

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.commute_hom_of_generators {H : Type*} [Group H] (f : G →* H) (S : Set G)
    (hS : Subgroup.closure S = ⊤)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, Commute (f x) (f y)) :
    ∀ x y : G, Commute (f x) (f y) := by sorry
