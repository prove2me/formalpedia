-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_Row_eval_cons
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.Row.eval_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:52.726958+00:00
-- url     : https://prove2.me/theorems/0a0a476a-6292-4e97-a65a-33928e620889
-- title:
--   Row: eval cons
-- statement:
--   The Row construction uses the eval cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L52-L55
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L52-L55

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.Row.eval_cons {n : ℕ} (r : Row (n + 1)) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (t : K) (x : Fin n → K) :
    r.eval (Fin.cons t x) = (r.head : K) * t + r.tail.eval x := by sorry
