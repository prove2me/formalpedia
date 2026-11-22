-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:38.70219+00:00
-- url     : https://prove2.me/theorems/e6e1568b-0c49-4c2e-b0ae-e5824bbc4524
-- title:
--   Computable Isomorphism: interpret encode Images get D
-- statement:
--   The Computable Isomorphism construction uses the interpret encode Images get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L86-L89
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L86-L89

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD {n m : ℕ} (f : Fin n → FreeGroup (Fin m))
    (i : Fin n) : interpretWord m ((encodeImages f).getD i.val []) = f i := by sorry
