-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.check_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:10:42.675018+00:00
-- url     : https://prove2.me/theorems/24103edc-e944-4164-bedb-982440aff424
-- title:
--   Computable Cover Data: check primrec
-- statement:
--   The Computable Cover Data construction uses the check primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L159-L161
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L159-L161

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.check_primrec : Primrec₂ check := by sorry
