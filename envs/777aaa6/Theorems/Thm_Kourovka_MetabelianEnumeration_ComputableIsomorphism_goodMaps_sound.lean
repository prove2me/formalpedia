-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_sound
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.goodMaps_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:51.050595+00:00
-- url     : https://prove2.me/theorems/d821e234-2b69-43cd-85cc-4a9667b7c6b4
-- title:
--   Computable Isomorphism: good Maps sound
-- statement:
--   The Computable Isomorphism construction uses the good Maps sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L28-L54
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L28-L54

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.goodMaps_sound (pq : PresentationCode × PresentationCode) (fg : Maps)
    (hv : validMaps (pq, fg)) (hg : GoodMaps pq fg) :
    Nonempty (GroupOf pq.1 ≃* GroupOf pq.2) := by sorry
