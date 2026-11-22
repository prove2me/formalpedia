-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.abelianQuotientMap_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:46.905828+00:00
-- url     : https://prove2.me/submissions/107281e5-bff4-48a4-b20d-bd00f81ab60e

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {α : Type} (R : List (FreeGroup α)) (a : α) :
    abelianQuotientMap R (Multiplicative.ofAdd (FreeAbelianGroup.of a)) =
      Abelianization.of (PresentedGroup.of a) := by
  change Additive.toMul ((FreeAbelianGroup.lift (fun a => Additive.ofMul
    (Abelianization.of (PresentedGroup.of (rels := {r | r ∈ R}) a))))
      (FreeAbelianGroup.of a)) = _
  rw [FreeAbelianGroup.lift_apply_of]
  rfl
end Kourovka.MetabelianEnumeration.CofinalCover
