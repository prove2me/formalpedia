-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.check_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:39.551171+00:00
-- url     : https://prove2.me/theorems/f5b56d78-9eb8-46ae-b5ee-e77d196bdae4
-- title:
--   Computable Fourier Motzkin: check eq
-- statement:
--   The Computable Fourier Motzkin construction uses the check eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L142-L151
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L142-L151

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.check_eq (n : ℕ) (rows : List RowCode) :
    check n rows = FourierMotzkin.check n (rows.map (decodeRow n)) := by sorry
