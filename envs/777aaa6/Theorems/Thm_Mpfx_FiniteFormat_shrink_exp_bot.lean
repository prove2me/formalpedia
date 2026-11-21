-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_bot
-- name    : Mpfx.FiniteFormat.shrink_exp_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:47.711951+00:00
-- url     : https://prove2.me/theorems/902f979b-c77e-421c-8411-f7e5bafea1c8
-- title:
--   Finite Format: shrink exp bot
-- statement:
--   The Finite Format construction uses the shrink exp bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L605-L607
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L605-L607

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.shrink_exp_bot {F : FiniteFormat} (h : F.p ≠ ((1 : ℕ) : Prec))
    (he : F.exp = ⊥) : (F.shrink h).exp = ⊥ := by sorry
