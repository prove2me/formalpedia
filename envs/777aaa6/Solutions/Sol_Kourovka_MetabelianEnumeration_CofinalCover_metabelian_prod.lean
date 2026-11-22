-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.metabelian_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:39.218025+00:00
-- url     : https://prove2.me/submissions/133d8515-a2c6-4bca-afae-21ad1f804ece

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (hG : Metabelian G) (hH : Metabelian H) : Metabelian (G × H) := by
  intro a b c d
  apply Prod.ext
  · exact (hG a.1 b.1 c.1 d.1).eq
  · exact (hH a.2 b.2 c.2 d.2).eq
end Kourovka.MetabelianEnumeration.CofinalCover
