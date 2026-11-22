-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverSemantics.code_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:53.703787+00:00
-- url     : https://prove2.me/submissions/9c7c271a-82b8-40e1-a7d7-a34bd2e02ece

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics
theorem _root_.solution (data : DatumCode) (R : ℕ) :
    Subgroup.closure (Set.range (codeT data R) ∪ Set.range (codeA data R)) = ⊤ := by
  have he : Set.range (codeT data R) ∪ Set.range (codeA data R) =
      Set.range (PresentedGroup.of (rels := relations (presentation data R))) := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Fin.castAdd (alphabet data) i, rfl⟩
      · exact ⟨Fin.natAdd (dimension data) i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i using Fin.addCases with
      | left j => exact Or.inl ⟨j, rfl⟩
      | right j => exact Or.inr ⟨j, rfl⟩
  rw [he]
  exact PresentedGroup.closure_range_of _
end Kourovka.MetabelianEnumeration.ComputableCoverSemantics
