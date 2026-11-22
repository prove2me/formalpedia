-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkIso_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkIso_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:41.531404+00:00
-- url     : https://prove2.me/theorems/c527958a-c955-449b-b042-2ce85260ca36
-- title:
--   Computable Isomorphism: check Iso primrec
-- statement:
--   The Computable Isomorphism construction uses the check Iso primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L97-L99
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L97-L99

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkIso_primrec : Primrec₂ checkIso := by sorry
