-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkEpi_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:53.370417+00:00
-- url     : https://prove2.me/theorems/f480ab91-5eee-42cd-8190-217ae83dded2
-- title:
--   Computable Epimorphism: check Epi primrec
-- statement:
--   The Computable Epimorphism construction uses the check Epi primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L51-L53
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean#L51-L53

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_primrec : Primrec₂ checkEpi := by sorry
