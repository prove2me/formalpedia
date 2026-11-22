-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_checkMargin_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:35.569471+00:00
-- url     : https://prove2.me/theorems/e21aa477-0c1d-4078-8ec3-93eb6cec6698
-- title:
--   Computable Cone: check Margin eq
-- statement:
--   The Computable Cone construction uses the check Margin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L191-L194
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L191-L194

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_eq (nr : ℕ × ℕ) (supports : SupportsCode) :
    checkMargin nr supports =
      ConeVerifier.checkMargin (decodeSupports nr.1 supports) ((1 / 2 : ℚ) ^ nr.2) := by sorry
