-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_prependChoices_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.prependChoices_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:21.312499+00:00
-- url     : https://prove2.me/theorems/684a9071-7295-4e29-a2c9-461129a2e5c2
-- title:
--   Computable Cone: prepend Choices primrec
-- statement:
--   The Computable Cone construction uses the prepend Choices primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L242-L247
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L242-L247

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.prependChoices_primrec : Primrec₂ prependChoices := by sorry
