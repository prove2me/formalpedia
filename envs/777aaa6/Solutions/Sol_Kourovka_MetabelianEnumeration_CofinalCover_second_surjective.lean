-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.second_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:20.492847+00:00
-- url     : https://prove2.me/submissions/272a2302-fa7f-4fd3-8b4d-cd2c123619e7

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (p : G →* Q) (q : H →* Q) (hp : Function.Surjective p) :
    Function.Surjective (second p q) := by
  intro h
  obtain ⟨g, hg⟩ := hp (q h)
  exact ⟨⟨(g, h), hg⟩, rfl⟩
end Kourovka.MetabelianEnumeration.CofinalCover
