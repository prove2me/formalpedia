-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.checkTrivial_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:37.206456+00:00
-- url     : https://prove2.me/submissions/98e7bcc9-18e9-4695-b187-351b98218c72

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_natural_word_trivial_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_checkNat_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution (input : PresentationCode × List (ℕ × Bool)) :
    (∃ certificate, checkTrivial input certificate = true) ↔
      validInput input ∧
        PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1 := by
  simp only [checkTrivial, Bool.and_eq_true, decide_eq_true_eq, exists_and_left]
  rw [ComputableClosure.checkNat_correct]
  constructor
  · rintro ⟨hvalid, hw⟩
    exact ⟨hvalid, (natural_word_trivial_iff _ hvalid.1 _ hvalid.2).mp hw⟩
  · rintro ⟨hvalid, hw⟩
    exact ⟨hvalid, (natural_word_trivial_iff _ hvalid.1 _ hvalid.2).mpr hw⟩
end Kourovka.MetabelianEnumeration.ComputablePresentations
