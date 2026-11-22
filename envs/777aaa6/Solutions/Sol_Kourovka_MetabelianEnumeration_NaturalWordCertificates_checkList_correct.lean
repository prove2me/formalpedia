-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordCertificates.checkList_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:48.621116+00:00
-- url     : https://prove2.me/submissions/4145a666-56bd-48e5-aec1-d57036a8140c

import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_checkTrivial_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordCertificates
open ComputablePresentations NaturalWordSubstitution
namespace Kourovka.MetabelianEnumeration.NaturalWordCertificates
theorem _root_.solution (inputs : List Input) :
    (∃ certs, checkList inputs certs = true) ↔ ∀ input ∈ inputs, Good input := by
  constructor
  · rintro ⟨cs, hcs⟩ input hi
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hi
    have h := of_decide_eq_true hcs i.val (List.mem_range.mpr i.isLt)
    have he : inputs.getD i.val ((0, []), []) = inputs.get i := by
      simp only [List.getD_eq_getElem _ _ i.isLt, List.get_eq_getElem]
    rw [he] at h
    exact (checkTrivial_correct _).mp ⟨_, h⟩
  · intro h
    choose cs hcs using fun i : Fin inputs.length =>
      (checkTrivial_correct (inputs.get i)).mpr (h _ (List.get_mem _ _))
    refine ⟨List.ofFn cs, ?_⟩
    apply decide_eq_true
    intro i hi
    have hi' : i < inputs.length := List.mem_range.mp hi
    have hcget : (List.ofFn cs).getD i 0 = cs ⟨i, hi'⟩ := by
      rw [List.getD_eq_getElem (List.ofFn cs) 0 (by simpa using hi')]
      simp
    simpa only [List.getD_eq_getElem inputs _ hi', hcget, List.get_eq_getElem] using hcs ⟨i, hi'⟩
end Kourovka.MetabelianEnumeration.NaturalWordCertificates
