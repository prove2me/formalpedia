-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_wellFormed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:20.220005+00:00
-- url     : https://prove2.me/theorems/3a2ff915-f41c-4a5c-a059-07ea9d7e956f
-- title:
--   Computable Isomorphism: encode Images well Formed
-- statement:
--   The Computable Isomorphism construction uses the encode Images well Formed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L80-L84
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L80-L84

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_wellFormed {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) :
    WellFormed (m, encodeImages f) := by sorry
