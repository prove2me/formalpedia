-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_vectorLength_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.vectorLength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:45.156915+00:00
-- url     : https://prove2.me/theorems/c74ac048-f062-4720-a1f8-a82543237388
-- title:
--   Computable Cover Data: vector Length eq
-- statement:
--   The Computable Cover Data construction uses the vector Length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L80-L84
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L80-L84

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.vectorLength_eq (k : ℕ) (v : List ℤ) :
    (vectorLength k v : ℚ) = supportLength (fun i : Fin k => v.getD i 0) := by sorry
