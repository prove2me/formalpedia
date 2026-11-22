-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_subNat_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.subNat_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:59.398992+00:00
-- url     : https://prove2.me/theorems/382953bd-708b-4057-b4a0-9d737ad5ec45
-- title:
--   Computable Integers: sub Nat eq
-- statement:
--   The Computable Integers construction uses the sub Nat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L43-L45
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L43-L45

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.subNat_eq (m n : ℕ) : subNat m n = (m : ℤ) - n := by sorry
