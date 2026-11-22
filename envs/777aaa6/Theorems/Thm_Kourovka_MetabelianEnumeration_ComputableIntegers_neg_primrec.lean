-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_neg_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.neg_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:27.565213+00:00
-- url     : https://prove2.me/theorems/034d90d0-cee1-429d-852a-416bb318636c
-- title:
--   Computable Integers: neg primrec
-- statement:
--   The Computable Integers construction uses the neg primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L53-L60
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L53-L60

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.neg_primrec : Primrec (fun z : ℤ => -z) := by sorry
