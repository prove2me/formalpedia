-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_source_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.source_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:00.281328+00:00
-- url     : https://prove2.me/theorems/35ef82ac-3d26-4cd1-a8ec-a2e95f8a388e
-- title:
--   Computable Enumeration: source primrec
-- statement:
--   The Computable Enumeration construction uses the source primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L38-L41
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L38-L41

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.source_primrec : Primrec source := by sorry
