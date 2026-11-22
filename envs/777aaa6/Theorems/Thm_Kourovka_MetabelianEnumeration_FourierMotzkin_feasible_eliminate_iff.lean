-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_feasible_eliminate_iff
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.feasible_eliminate_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:05.952181+00:00
-- url     : https://prove2.me/theorems/445f08f1-4a43-4ccf-9e20-c991928fdf6d
-- title:
--   Fourier Motzkin: feasible eliminate iff
-- statement:
--   The Fourier Motzkin construction uses the feasible eliminate iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L196-L205
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L196-L205

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.feasible_eliminate_iff {n : ℕ} (rows : List (Row (n + 1)))
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Feasible (eliminate rows) K ↔ Feasible rows K := by sorry
