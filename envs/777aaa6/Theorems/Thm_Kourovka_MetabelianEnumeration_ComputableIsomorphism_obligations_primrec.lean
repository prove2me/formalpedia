-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_obligations_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.obligations_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:44.402615+00:00
-- url     : https://prove2.me/theorems/8ab729ff-ef4a-426e-8954-c26562d832f1
-- title:
--   Computable Isomorphism: obligations primrec
-- statement:
--   The Computable Isomorphism construction uses the obligations primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L72-L81
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L72-L81

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.obligations_primrec : Primrec obligations := by sorry
