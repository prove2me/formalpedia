-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CentralExtension.lift_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:16.181835+00:00
-- url     : https://prove2.me/submissions/7728de4e-981c-4ebc-b10a-b84b1604acfa

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_Presentations_CentralExtension

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]
omit [Fintype α] [Fintype β]
namespace Kourovka.MetabelianEnumeration.CentralExtension
theorem _root_.solution {H : Type*} [Group H] (f : α → H) (g : β → H)
    (w : FreeGroup α) :
    FreeGroup.lift (Sum.elim f g) (FreeGroup.map Sum.inl w) = FreeGroup.lift f w := by
  have h : (FreeGroup.lift (Sum.elim f g)).comp (FreeGroup.map Sum.inl) =
      FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h w
end Kourovka.MetabelianEnumeration.CentralExtension
