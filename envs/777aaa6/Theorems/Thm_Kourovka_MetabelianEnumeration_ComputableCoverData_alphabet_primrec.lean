-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_alphabet_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.alphabet_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:23.826189+00:00
-- url     : https://prove2.me/theorems/54a3cd45-7874-46f1-84c9-f1eb72f127c6
-- title:
--   Computable Cover Data: alphabet primrec
-- statement:
--   The Computable Cover Data construction uses the alphabet primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L122-L123
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L122-L123

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.alphabet_primrec : Primrec alphabet := by sorry
