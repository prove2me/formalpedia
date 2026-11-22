-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_pair_constraint
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.pair_constraint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:57.779192+00:00
-- url     : https://prove2.me/theorems/39b6c3a8-1cd1-417e-9352-8587a56fb9d7
-- title:
--   Fourier Motzkin: pair constraint
-- statement:
--   The Fourier Motzkin construction uses the pair constraint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L113-L118
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L113-L118

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.pair_constraint {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b c d : K} (ha : a < 0) (hc : 0 < c) :
    c * b - a * d ≤ 0 ↔ -b / a ≤ -d / c := by sorry
