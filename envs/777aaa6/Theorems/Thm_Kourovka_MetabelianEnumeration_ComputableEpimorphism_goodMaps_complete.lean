-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_goodMaps_complete
-- name    : Kourovka.MetabelianEnumeration.ComputableEpimorphism.goodMaps_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:04:55.460573+00:00
-- url     : https://prove2.me/theorems/de6da01f-f270-41a2-9a1c-765414586d56
-- title:
--   Computable Epimorphism: good Maps complete
-- statement:
--   Every actual surjection has finite words witnessing its generator images
--   and preimages, and hence finite proofs of all checker obligations.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean#L73-L107
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean#L73-L107

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_complete
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)

theorem Kourovka.MetabelianEnumeration.ComputableEpimorphism.goodMaps_complete (p q : PresentationCode) (hp : WellFormed p) (hq : WellFormed q)
    (e : GroupOf p →* GroupOf q) (he : Function.Surjective e) :
    ∃ fg : Maps, validMaps ((p, q), fg) ∧ GoodMaps (p, q) fg := by sorry
