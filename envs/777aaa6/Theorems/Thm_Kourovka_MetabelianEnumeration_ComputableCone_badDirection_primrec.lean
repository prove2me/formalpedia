-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_badDirection_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.badDirection_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:46.793297+00:00
-- url     : https://prove2.me/theorems/26961f10-88e3-46a9-802c-eab4a1947456
-- title:
--   Computable Cone: bad Direction primrec
-- statement:
--   The Computable Cone construction uses the bad Direction primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L261-L284
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L261-L284

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
set_option maxHeartbeats 2000000

theorem Kourovka.MetabelianEnumeration.ComputableCone.badDirection_primrec : Primrec₂ badDirection := by sorry
