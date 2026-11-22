-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkData_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:00.765224+00:00
-- url     : https://prove2.me/submissions/3e7ff9df-14cc-4d20-a2f0-235a66c74240

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordCertificates_checkList_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∃ cs, checkData pq (fg, cs) = true) ↔
      validMaps (pq, fg) ∧ ∀ input ∈ obligations (pq, fg), Good input := by
  simp only [checkData, Bool.and_eq_true, decide_eq_true_eq, exists_and_left]
  rw [checkList_correct]
end Kourovka.MetabelianEnumeration.ComputableEpimorphism
