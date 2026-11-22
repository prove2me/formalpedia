-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.check_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:29.816395+00:00
-- url     : https://prove2.me/theorems/d2c8c5bd-e280-4062-85bf-21d98b250596
-- title:
--   Fourier Motzkin: check correct
-- statement:
--   The Fourier Motzkin construction uses the check correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L212-L228
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L212-L228

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.check_correct (n : ℕ) (rows : List (Row n))
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    check n rows = true ↔ Feasible rows K := by sorry
