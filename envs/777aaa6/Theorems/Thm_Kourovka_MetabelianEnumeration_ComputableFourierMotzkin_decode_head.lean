-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_head
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:22.613414+00:00
-- url     : https://prove2.me/theorems/ffc4885a-b65f-4b6f-81b6-7c7449323bb3
-- title:
--   Computable Fourier Motzkin: decode head
-- statement:
--   The Computable Fourier Motzkin construction uses the decode head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L90-L90
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L90-L90

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_head (n : ℕ) (r : RowCode) : (decodeRow (n + 1) r).head = (head r : ℚ) := by sorry
