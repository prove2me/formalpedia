-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_combined_correction
-- name    : Kourovka.MetabelianEnumeration.CentralExtension.combined_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:48.38996+00:00
-- url     : https://prove2.me/theorems/02145c78-a241-4c6c-941c-511084e445a0
-- title:
--   Central Extension: combined correction
-- statement:
--   The Central Extension construction uses the combined correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean#L36-L42
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean#L36-L42

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_Presentations_CentralExtension
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]

theorem Kourovka.MetabelianEnumeration.CentralExtension.combined_correction (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (r : FreeGroup α) (hr : r ∈ R) :
    PresentedGroup.mk (relSet (combinedRelations R S c)) (FreeGroup.map Sum.inl r) =
      PresentedGroup.mk (relSet (combinedRelations R S c)) (FreeGroup.map Sum.inr (c r)) := by sorry
