-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.ofNat_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:21.982361+00:00
-- url     : https://prove2.me/theorems/47584f43-74e5-415c-a5de-1716185b1cff
-- title:
--   Computable Integers: of Nat primrec
-- statement:
--   The Computable Integers construction uses the of Nat primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L19-L20
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L19-L20

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.ofNat_primrec : Primrec (fun n : ℕ => (n : ℤ)) := by sorry
