-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_badDirection_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.badDirection_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:08.958535+00:00
-- url     : https://prove2.me/theorems/28138816-eafe-40fd-a45b-e54f5b4ebb38
-- title:
--   Computable Cone: bad Direction eq
-- statement:
--   The Computable Cone construction uses the bad Direction eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L162-L189
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L162-L189

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.badDirection_eq (nr : ℕ × ℕ) (supports : SupportsCode) :
    badDirection nr supports =
      ConeVerifier.badDirection (decodeSupports nr.1 supports) ((1 / 2 : ℚ) ^ nr.2) := by sorry
