-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_complete
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.goodMaps_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:58.771199+00:00
-- url     : https://prove2.me/theorems/7c55cb77-f99e-4828-b097-adfb4c80a0b9
-- title:
--   Computable Isomorphism: good Maps complete
-- statement:
--   Every actual ordinary-presentation isomorphism admits finite natural
--   words satisfying all relator and inverse-generator equations.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L93-L134
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L93-L134

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.goodMaps_complete (p q : PresentationCode) (hp : WellFormed p) (hq : WellFormed q)
    (e : GroupOf p ≃* GroupOf q) :
    ∃ fg : Maps, validMaps ((p, q), fg) ∧ GoodMaps (p, q) fg := by sorry
