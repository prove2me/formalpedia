-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkData_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkData_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:06:48.986039+00:00
-- url     : https://prove2.me/theorems/4f085146-694f-45f8-a82c-114e8d34e26a
-- title:
--   Computable Epimorphism: check Data correct
-- statement:
--   The Computable Epimorphism construction uses the check Data correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L55-L59
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L55-L59

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_correct

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkData_correct (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∃ cs, checkData pq (fg, cs) = true) ↔
      validMaps (pq, fg) ∧ ∀ input ∈ obligations (pq, fg), Good input := by sorry
