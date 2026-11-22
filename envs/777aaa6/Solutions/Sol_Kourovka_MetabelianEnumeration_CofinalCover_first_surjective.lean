-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.first_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:45:55.083181+00:00
-- url     : https://prove2.me/submissions/1880c93d-fcf4-4827-8863-71a698e80c9d

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (p : G →* Q) (q : H →* Q) (hq : Function.Surjective q) :
    Function.Surjective (first p q) := by
  intro g
  obtain ⟨h, hh⟩ := hq (p g)
  exact ⟨⟨(g, h), hh.symm⟩, rfl⟩
end Kourovka.MetabelianEnumeration.CofinalCover
