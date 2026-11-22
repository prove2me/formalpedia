-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.group_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:55:13.282183+00:00
-- url     : https://prove2.me/submissions/fca0589a-5700-48fb-9325-3e4e34d2df0e

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (R : ℕ) :
    Subgroup.closure (Set.range (groupT data R) ∪ Set.range (groupA data R)) = ⊤ := by
  have he : Set.range (groupT data R) ∪ Set.range (groupA data R) =
      Set.range (PresentedGroup.of (rels := WordCertificates.relSet (relators data R))) := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Fin.castAdd a i, rfl⟩
      · exact ⟨Fin.natAdd k i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i using Fin.addCases with
      | left j => exact Or.inl ⟨j, rfl⟩
      | right j => exact Or.inr ⟨j, rfl⟩
  rw [he]
  exact PresentedGroup.closure_range_of _
end Kourovka.MetabelianEnumeration.FiniteCover
