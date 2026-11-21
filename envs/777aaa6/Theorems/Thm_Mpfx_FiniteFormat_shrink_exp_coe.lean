-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_coe
-- name    : Mpfx.FiniteFormat.shrink_exp_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:07.860518+00:00
-- url     : https://prove2.me/theorems/6c5e305b-b685-426f-bb68-85b060f23a07
-- title:
--   Finite Format: shrink exp coe
-- statement:
--   The Finite Format construction uses the shrink exp coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L601-L603
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L601-L603

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.shrink_exp_coe {F : FiniteFormat} (h : F.p ≠ ((1 : ℕ) : Prec)) {e : ℤ}
    (he : F.exp = (e : QExp)) : (F.shrink h).exp = ((e + 1 : ℤ) : QExp) := by sorry
