-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decodeCertificate_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.decodeCertificate_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:52.918583+00:00
-- url     : https://prove2.me/theorems/2894fdf8-cf06-46bc-b474-38dafc9540bd
-- title:
--   Computable Enumeration: decode Certificate primrec
-- statement:
--   The Computable Enumeration construction uses the decode Certificate primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L73-L74
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L73-L74

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.decodeCertificate_primrec : Primrec decodeCertificate := by sorry
