-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_decodePresentation_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.decodePresentation_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:20.962519+00:00
-- url     : https://prove2.me/theorems/a5090a27-c649-4838-844e-05e7c1b2250e
-- title:
--   Computable Presentations: decode Presentation primrec
-- statement:
--   The Computable Presentations construction uses the decode Presentation primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L24-L25
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L24-L25

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.decodePresentation_primrec : Primrec decodePresentation := by sorry
