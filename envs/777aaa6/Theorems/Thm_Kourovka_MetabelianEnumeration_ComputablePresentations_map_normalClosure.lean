-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_map_normalClosure
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.map_normalClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:12.389528+00:00
-- url     : https://prove2.me/theorems/5cbcada8-b0fe-4535-9005-056559894312
-- title:
--   Computable Presentations: map normal Closure
-- statement:
--   The Computable Presentations construction uses the map normal Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L65-L69
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L65-L69

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.map_normalClosure {G H : Type*} [Group G] [Group H]
    (f : G →* H) (S : Set G) (T : Set H)
    (h : ∀ r ∈ S, f r ∈ Subgroup.normalClosure T) {x : G}
    (hx : x ∈ Subgroup.normalClosure S) : f x ∈ Subgroup.normalClosure T := by sorry
