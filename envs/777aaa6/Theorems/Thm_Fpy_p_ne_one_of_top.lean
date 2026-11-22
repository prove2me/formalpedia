-- Prove2me | Theorems.Thm_Fpy_p_ne_one_of_top
-- name    : Fpy.p_ne_one_of_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:54.808177+00:00
-- url     : https://prove2.me/theorems/599bb2aa-9ad2-4e42-afa1-e3eafc252cdd
-- title:
--   Fpy: p ne one of top
-- statement:
--   The Fpy construction uses the p ne one of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L78-L79
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L78-L79

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.p_ne_one_of_top {F : FiniteFormat} (h : F.p = ⊤) : F.p ≠ ((1 : ℕ) : Prec) := by sorry
