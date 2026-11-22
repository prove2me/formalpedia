-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:34.435582+00:00
-- url     : https://prove2.me/theorems/f4159d3e-2e76-4c49-8845-775e105446af
-- title:
--   Computable Isomorphism: encode Images length
-- statement:
--   The Computable Isomorphism construction uses the encode Images length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L77-L78
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L77-L78

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) :
    (encodeImages f).length = n := by sorry
