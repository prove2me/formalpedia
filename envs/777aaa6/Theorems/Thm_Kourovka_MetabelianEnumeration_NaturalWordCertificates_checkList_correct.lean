-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordCertificates_checkList_correct
-- name    : Kourovka.MetabelianEnumeration.NaturalWordCertificates.checkList_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:53.250686+00:00
-- url     : https://prove2.me/theorems/e127429a-de45-40b5-9532-2bd6678e55d8
-- title:
--   Natural Word Certificates: check List correct
-- statement:
--   The Natural Word Certificates construction uses the check List correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordCertificates.lean#L38-L58
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordCertificates.lean#L38-L58

import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordCertificates
open ComputablePresentations NaturalWordSubstitution

theorem Kourovka.MetabelianEnumeration.NaturalWordCertificates.checkList_correct (inputs : List Input) :
    (∃ certs, checkList inputs certs = true) ↔ ∀ input ∈ inputs, Good input := by sorry
