-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_naturalRelators_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.naturalRelators_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:05.525695+00:00
-- url     : https://prove2.me/theorems/8440639e-f986-44e7-9397-52c489045511
-- title:
--   Computable Presentations: natural Relators primrec
-- statement:
--   The Computable Presentations construction uses the natural Relators primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L29-L30
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L29-L30

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.naturalRelators_primrec : Primrec naturalRelators := by sorry
