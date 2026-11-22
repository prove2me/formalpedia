-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_lower_constraint
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.lower_constraint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:01.344971+00:00
-- url     : https://prove2.me/theorems/0d22e9be-00d4-4588-b465-b6407e08fba5
-- title:
--   Fourier Motzkin: lower constraint
-- statement:
--   The Fourier Motzkin construction uses the lower constraint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L101-L105
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L101-L105

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.lower_constraint {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b t : K} (ha : a < 0) :
    a * t + b ≤ 0 ↔ -b / a ≤ t := by sorry
