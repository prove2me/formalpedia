-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkEpi_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:04:23.468633+00:00
-- url     : https://prove2.me/theorems/18e89e31-73b4-4e2f-81dc-eed32f01f812
-- title:
--   Computable Epimorphism: check Epi correct
-- statement:
--   The Computable Epimorphism construction uses the check Epi correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean#L109-L123
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean#L109-L123

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)

theorem Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_correct (pq : PresentationCode × PresentationCode) :
    (∃ n, checkEpi pq n = true) ↔
      WellFormed pq.1 ∧ WellFormed pq.2 ∧
        ∃ F : GroupOf pq.1 →* GroupOf pq.2, Function.Surjective F := by sorry
