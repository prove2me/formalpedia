-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkData_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkData_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:07:14.127605+00:00
-- url     : https://prove2.me/theorems/fe6ad794-1f2b-4123-8a53-c4a190012e32
-- title:
--   Computable Epimorphism: check Data primrec
-- statement:
--   The Computable Epimorphism construction uses the check Data primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L40-L44
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L40-L44

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkData_primrec : Primrec₂ checkData := by sorry
