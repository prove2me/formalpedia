-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkData_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:47.904853+00:00
-- url     : https://prove2.me/submissions/cf951754-bbb2-4ee1-a3a7-d083c40e02ab

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordCertificates_checkList_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∃ cs, checkData pq (fg, cs) = true) ↔
      validMaps (pq, fg) ∧ ∀ input ∈ obligations (pq, fg), Good input := by
  simp only [checkData, Bool.and_eq_true, decide_eq_true_eq, exists_and_left]
  rw [checkList_correct]
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
