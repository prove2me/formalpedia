-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkData_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:28.788705+00:00
-- url     : https://prove2.me/theorems/89f87d75-e470-450c-a037-e57a81694987
-- title:
--   Computable Isomorphism: check Data correct
-- statement:
--   The Computable Isomorphism construction uses the check Data correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L101-L105
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L101-L105

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkData_correct (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∃ cs, checkData pq (fg, cs) = true) ↔
      validMaps (pq, fg) ∧ ∀ input ∈ obligations (pq, fg), Good input := by sorry
