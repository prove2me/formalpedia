-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_metabelian_surjective
-- name    : Kourovka.MetabelianEnumeration.metabelian_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:22.577885+00:00
-- url     : https://prove2.me/theorems/3ad5a91e-6d99-48d0-831e-a0e32cb82fad
-- title:
--   Metabelian Enumeration: metabelian surjective
-- statement:
--   A surjective homomorphic image of a metabelian group is metabelian.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/Presentations.lean#L51-L58
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/Presentations.lean#L51-L58

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Definitions.Def_Kourovka_Presentations_Presentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.metabelian_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : Metabelian G) : Metabelian H := by sorry
