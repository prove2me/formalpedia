-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.metabelian_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:30.414651+00:00
-- url     : https://prove2.me/submissions/47aa96dd-967b-4e69-a26c-a11d83824965

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {E : Type} [Group E] (f : E →* G)
    (hf : Function.Injective f) (hG : Metabelian G) : Metabelian E := by
  intro a b c d
  apply hf
  simpa only [map_mul, map_commutatorElement] using (hG (f a) (f b) (f c) (f d)).eq
end Kourovka.MetabelianEnumeration.CofinalCover
