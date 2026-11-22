-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_Row_eval_combine
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.Row.eval_combine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:52.258183+00:00
-- url     : https://prove2.me/theorems/88bf10e3-0d18-4026-a0be-9f0c70bd4710
-- title:
--   Row: eval combine
-- statement:
--   The Row construction uses the eval combine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L57-L64
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L57-L64

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.Row.eval_combine {n : ℕ} (l u : Row (n + 1)) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (x : Fin n → K) :
    (l.combine u).eval x = (u.head : K) * l.tail.eval x -
      (l.head : K) * u.tail.eval x := by sorry
