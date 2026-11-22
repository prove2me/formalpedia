-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_inverseChecks_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.inverseChecks_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:47.363062+00:00
-- url     : https://prove2.me/theorems/8f3f7093-3a23-49c3-a7ab-df58564c13af
-- title:
--   Computable Isomorphism: inverse Checks primrec
-- statement:
--   The Computable Isomorphism construction uses the inverse Checks primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L55-L64
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean#L55-L64

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.inverseChecks_primrec : Primrec inverseChecks := by sorry
