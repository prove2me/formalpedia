-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordCertificates_checkList_primrec
-- name    : Kourovka.MetabelianEnumeration.NaturalWordCertificates.checkList_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:48.492621+00:00
-- url     : https://prove2.me/theorems/e04315b4-60d8-4b73-bd27-2c71ce170547
-- title:
--   Natural Word Certificates: check List primrec
-- statement:
--   The Natural Word Certificates construction uses the check List primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordCertificates.lean#L24-L33
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordCertificates.lean#L24-L33

import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordCertificates
open ComputablePresentations NaturalWordSubstitution

theorem Kourovka.MetabelianEnumeration.NaturalWordCertificates.checkList_primrec : Primrec₂ checkList := by sorry
