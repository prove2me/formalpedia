-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkIso_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkIso_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:00.936861+00:00
-- url     : https://prove2.me/theorems/99a35d7f-e92e-46af-a331-30090cf0e0fd
-- title:
--   Computable Isomorphism: check Iso correct
-- statement:
--   The Computable Isomorphism construction uses the check Iso correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L136-L149
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L136-L149

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkIso_correct (pq : PresentationCode × PresentationCode) :
    (∃ n, checkIso pq n = true) ↔
      WellFormed pq.1 ∧ WellFormed pq.2 ∧ Nonempty (GroupOf pq.1 ≃* GroupOf pq.2) := by sorry
