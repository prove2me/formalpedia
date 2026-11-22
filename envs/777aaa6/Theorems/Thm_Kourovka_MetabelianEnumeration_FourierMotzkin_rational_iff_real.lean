-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_rational_iff_real
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.rational_iff_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:01:43.362492+00:00
-- url     : https://prove2.me/theorems/504e7f9b-51b7-400d-8635-8716505155b5
-- title:
--   Fourier Motzkin: rational iff real
-- statement:
--   Rational inequalities have a rational solution exactly when they have a real solution.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L231-L233
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L231-L233

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.rational_iff_real {n : ℕ} (rows : List (Row n)) :
    Feasible rows ℚ ↔ Feasible rows ℝ := by sorry
