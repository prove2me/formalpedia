-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_obligations_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEpimorphism.obligations_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:59.395517+00:00
-- url     : https://prove2.me/theorems/2af0a69e-1342-41f2-bbc6-43a9f1d141c9
-- title:
--   Computable Epimorphism: obligations primrec
-- statement:
--   The Computable Epimorphism construction uses the obligations primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L28-L35
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L28-L35

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_obligations_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableEpimorphism.obligations_primrec : Primrec obligations := by sorry
