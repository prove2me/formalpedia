-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_map_filter_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.map_filter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:32.808852+00:00
-- url     : https://prove2.me/theorems/6f2ce196-768f-41e0-8919-3db1bfa3c9d5
-- title:
--   Computable Fourier Motzkin: map filter eq
-- statement:
--   The Computable Fourier Motzkin construction uses the map filter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L116-L121
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L116-L121

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.map_filter_eq {α β : Type*} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (l : List α) :
    (l.filter p).map f = (l.map f).filter q := by sorry
