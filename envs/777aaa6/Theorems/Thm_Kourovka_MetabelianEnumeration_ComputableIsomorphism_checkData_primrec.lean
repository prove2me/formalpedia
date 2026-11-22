-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkData_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:09.341728+00:00
-- url     : https://prove2.me/theorems/e660af10-c676-47e1-a5a1-0bf605c1d7c5
-- title:
--   Computable Isomorphism: check Data primrec
-- statement:
--   The Computable Isomorphism construction uses the check Data primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L86-L90
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L86-L90

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkData_primrec : Primrec₂ checkData := by sorry
