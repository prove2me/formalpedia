-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_finite_presentation_of_central_extension
-- name    : Kourovka.MetabelianEnumeration.CentralExtension.finite_presentation_of_central_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:56.972336+00:00
-- url     : https://prove2.me/theorems/64ad32b0-9b7b-4c61-b05f-1ff4ca0364a7
-- title:
--   Central Extension: finite presentation of central extension
-- statement:
--   A central extension of two ordinary finitely presented groups has an
--   ordinary finite presentation, on the union of their finite alphabets.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtensionPresentation.lean#L20-L167
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtensionPresentation.lean#L20-L167

import Definitions.Def_Kourovka_Presentations_CentralExtension
import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]

theorem Kourovka.MetabelianEnumeration.CentralExtension.finite_presentation_of_central_extension
    (R : List (FreeGroup α)) (S : List (FreeGroup β))
    {E : Type} [Group E]
    (π : E →* PresentedGroup (relSet R))
    (ι : PresentedGroup (relSet S) →* E)
    (hπ : Function.Surjective π) (hι : Function.Injective ι)
    (hexact : ι.range = π.ker) (hcentral : ι.range ≤ Subgroup.center E) :
    ∃ T : List (FreeGroup (α ⊕ β)), Nonempty (PresentedGroup (relSet T) ≃* E) := by sorry
