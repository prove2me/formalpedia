-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_extended_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.extended_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:04.079042+00:00
-- url     : https://prove2.me/theorems/3e9d2038-7c2d-4a75-907c-65f43f47a4db
-- title:
--   Computable Enumeration: extended primrec
-- statement:
--   The Computable Enumeration construction uses the extended primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L43-L44
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L43-L44

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.extended_primrec : Primrec extended := by sorry
