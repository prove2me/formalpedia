-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_validMaps_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.validMaps_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:44.531396+00:00
-- url     : https://prove2.me/theorems/9345209b-0118-4eaa-8bc6-d158f03322ec
-- title:
--   Computable Isomorphism: valid Maps primrec
-- statement:
--   The Computable Isomorphism construction uses the valid Maps primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L31-L40
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L31-L40

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.validMaps_primrec : PrimrecPred validMaps := by sorry
