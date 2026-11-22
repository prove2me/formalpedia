-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CentralExtension.lift_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:20.047681+00:00
-- url     : https://prove2.me/submissions/5b751aa0-3bc3-4937-84ac-faac8773633c

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
    (w : FreeGroup β) :
    FreeGroup.lift (Sum.elim f g) (FreeGroup.map Sum.inr w) = FreeGroup.lift g w := by
  have h : (FreeGroup.lift (Sum.elim f g)).comp (FreeGroup.map Sum.inr) =
      FreeGroup.lift g := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h w
end Kourovka.MetabelianEnumeration.CentralExtension
