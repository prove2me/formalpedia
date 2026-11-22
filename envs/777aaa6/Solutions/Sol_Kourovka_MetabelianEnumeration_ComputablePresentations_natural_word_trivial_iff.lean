-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.natural_word_trivial_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:02.708567+00:00
-- url     : https://prove2.me/submissions/6c8e8661-0748-4e13-8f5a-282bc67239ee

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_restrict_mk
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_include_interpret
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_map_normalClosure

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution (p : PresentationCode) (hp : WellFormed p)
    (w : List (ℕ × Bool)) (hw : ∀ letter ∈ w, letter.1 < p.1) :
    FreeGroup.mk w ∈ Subgroup.normalClosure {r | r ∈ naturalRelators p} ↔
      PresentedGroup.mk (relations p) (interpretWord p.1 w) = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  constructor
  · intro h
    rw [← restrict_mk]
    apply map_normalClosure (restrictGenerators p.1) _ _ ?_ h
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rw [restrict_mk]
    apply Subgroup.subset_normalClosure
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  · intro h
    rw [← include_interpret p.1 w hw]
    apply map_normalClosure (includeGenerators p.1) _ _ ?_ h
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rw [include_interpret p.1 v (hp v hv)]
    apply Subgroup.subset_normalClosure
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
end Kourovka.MetabelianEnumeration.ComputablePresentations
