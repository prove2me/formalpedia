-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_lift_inl_eq
-- name    : Kourovka.MetabelianEnumeration.CentralExtension.lift_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:53.225582+00:00
-- url     : https://prove2.me/theorems/87ec84fc-3273-479a-a0c6-14a6f19c0555
-- title:
--   Central Extension: lift inl eq
-- statement:
--   The Central Extension construction uses the lift inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean#L79-L87
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean#L79-L87

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_Presentations_CentralExtension
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]
omit [Fintype α] [Fintype β]

theorem Kourovka.MetabelianEnumeration.CentralExtension.lift_inl_eq {H : Type*} [Group H] (f : α → H) (g : β → H)
    (w : FreeGroup α) :
    FreeGroup.lift (Sum.elim f g) (FreeGroup.map Sum.inl w) = FreeGroup.lift f w := by sorry
