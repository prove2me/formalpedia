-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_nat_pow_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.nat_pow_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:00.640497+00:00
-- url     : https://prove2.me/theorems/ef1e2092-0d96-468f-8665-834a05b594e0
-- title:
--   Computable Integers: nat pow primrec
-- statement:
--   The Computable Integers construction uses the nat pow primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L109-L116
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L109-L116

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.nat_pow_primrec : Primrec₂ (fun a n : ℕ => a ^ n) := by sorry
