-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_lift_inr_eq
-- name    : Kourovka.MetabelianEnumeration.CentralExtension.lift_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:49.936016+00:00
-- url     : https://prove2.me/theorems/cc00c204-5ee7-485d-9122-c803e688a251
-- title:
--   Central Extension: lift inr eq
-- statement:
--   The Central Extension construction uses the lift inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean#L90-L98
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean#L90-L98

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_Presentations_CentralExtension
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]
omit [Fintype α] [Fintype β]

theorem Kourovka.MetabelianEnumeration.CentralExtension.lift_inr_eq {H : Type*} [Group H] (f : α → H) (g : β → H)
    (w : FreeGroup β) :
    FreeGroup.lift (Sum.elim f g) (FreeGroup.map Sum.inr w) = FreeGroup.lift g w := by sorry
