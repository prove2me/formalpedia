-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_toNat_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.toNat_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:55.776578+00:00
-- url     : https://prove2.me/theorems/187fe580-4cf2-46b3-ba8d-5b1553293a57
-- title:
--   Computable Integers: to Nat primrec
-- statement:
--   The Computable Integers construction uses the to Nat primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L32-L34
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L32-L34

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.toNat_primrec : Primrec Int.toNat := by sorry
