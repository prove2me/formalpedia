-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_sound
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.check_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:00.352156+00:00
-- url     : https://prove2.me/theorems/036b0ee6-e4cf-44ed-bde1-8d82db9a852a
-- title:
--   Computable Cover Data: check sound
-- statement:
--   The Computable Cover Data construction uses the check sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L163-L167
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L163-L167

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.check_sound (data : DatumCode) (r : ℕ) (h : check data r = true) :
    Metabelian (FiniteCover.GroupOf (decode data) (radius data r)) := by sorry
