-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_subNat_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.subNat_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:09.966481+00:00
-- url     : https://prove2.me/theorems/71f8d0cf-550c-4dc2-82ac-ee59289d63f5
-- title:
--   Computable Integers: sub Nat primrec
-- statement:
--   The Computable Integers construction uses the sub Nat primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L47-L51
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L47-L51

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.subNat_primrec : Primrec₂ subNat := by sorry
