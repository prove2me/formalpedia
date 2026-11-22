-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_checkMargin_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:41.130261+00:00
-- url     : https://prove2.me/theorems/67182023-e1c0-4315-92d8-fab070dfea15
-- title:
--   Computable Cone: check Margin primrec
-- statement:
--   The Computable Cone construction uses the check Margin primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L286-L286
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L286-L286

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_primrec : Primrec₂ checkMargin := by sorry
