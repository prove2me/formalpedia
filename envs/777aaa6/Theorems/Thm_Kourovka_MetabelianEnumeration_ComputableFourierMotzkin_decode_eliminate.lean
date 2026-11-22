-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_eliminate
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_eliminate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:32.742007+00:00
-- url     : https://prove2.me/theorems/4248cea1-0f8c-48e2-9b10-dd9017a4b359
-- title:
--   Computable Fourier Motzkin: decode eliminate
-- statement:
--   The Computable Fourier Motzkin construction uses the decode eliminate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L123-L140
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L123-L140

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_eliminate (n : ℕ) (rows : List RowCode) :
    (eliminate rows).map (decodeRow n) =
      FourierMotzkin.eliminate (rows.map (decodeRow (n + 1))) := by sorry
