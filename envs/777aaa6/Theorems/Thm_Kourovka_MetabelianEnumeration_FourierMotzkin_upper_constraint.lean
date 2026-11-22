-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_upper_constraint
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.upper_constraint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:04.226276+00:00
-- url     : https://prove2.me/theorems/56248e0a-355f-4817-96ee-a8b70566b385
-- title:
--   Fourier Motzkin: upper constraint
-- statement:
--   The Fourier Motzkin construction uses the upper constraint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L107-L111
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L107-L111

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.upper_constraint {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b t : K} (ha : 0 < a) :
    a * t + b ≤ 0 ↔ t ≤ -b / a := by sorry
