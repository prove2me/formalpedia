-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_good_obligations
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.good_obligations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:38.067004+00:00
-- url     : https://prove2.me/theorems/6afe746d-46b7-429b-bda2-c06d77a5444f
-- title:
--   Computable Isomorphism: good obligations
-- statement:
--   The Computable Isomorphism construction uses the good obligations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L23-L26
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L23-L26

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.good_obligations (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∀ input ∈ obligations (pq, fg), Good input) ↔ GoodMaps pq fg := by sorry
