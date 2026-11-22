-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_lengthBound_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.lengthBound_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:04.279854+00:00
-- url     : https://prove2.me/theorems/97bc2903-60a0-4918-a6ee-a8e0c8bb42a4
-- title:
--   Computable Cover Data: length Bound primrec
-- statement:
--   The Computable Cover Data construction uses the length Bound primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L139-L144
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L139-L144

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.lengthBound_primrec : Primrec lengthBound := by sorry
