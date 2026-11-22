-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_lt_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.lt_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:30.611631+00:00
-- url     : https://prove2.me/theorems/a604166b-40f8-4b94-bff8-3e5b0af8d214
-- title:
--   Computable Integers: lt primrec
-- statement:
--   The Computable Integers construction uses the lt primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L87-L88
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L87-L88

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.lt_primrec : PrimrecRel (fun x y : ℤ => x < y) := by sorry
