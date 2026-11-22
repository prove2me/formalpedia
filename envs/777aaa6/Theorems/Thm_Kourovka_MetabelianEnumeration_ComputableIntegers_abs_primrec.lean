-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_abs_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.abs_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:01:14.195986+00:00
-- url     : https://prove2.me/theorems/eae55a72-4e01-4951-a2d7-47bfca0acaa4
-- title:
--   Computable Integers: abs primrec
-- statement:
--   The Computable Integers construction uses the abs primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L90-L91
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L90-L91

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.abs_primrec : Primrec (fun z : ℤ => |z|) := by sorry
