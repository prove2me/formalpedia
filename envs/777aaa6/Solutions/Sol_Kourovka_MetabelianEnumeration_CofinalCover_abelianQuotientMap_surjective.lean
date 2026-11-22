-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.abelianQuotientMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:24.390181+00:00
-- url     : https://prove2.me/submissions/b6375fed-e769-4428-9726-4ad66a65f81a

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_of

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {α : Type} (R : List (FreeGroup α)) :
    Function.Surjective (abelianQuotientMap R) := by
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have h : g ∈ (abelianQuotientMap R).range.comap Abelianization.of := by
    apply PresentedGroup.generated_by
    intro a
    exact ⟨Multiplicative.ofAdd (FreeAbelianGroup.of a), abelianQuotientMap_of R a⟩
  exact h
end Kourovka.MetabelianEnumeration.CofinalCover
