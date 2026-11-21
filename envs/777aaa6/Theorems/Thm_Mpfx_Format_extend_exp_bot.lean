-- Prove2me | Theorems.Thm_Mpfx_Format_extend_exp_bot
-- name    : Mpfx.Format.extend_exp_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:30.371908+00:00
-- url     : https://prove2.me/theorems/ffe1ecd8-7e71-4244-a347-dc356dced91e
-- title:
--   Format: extend exp bot
-- statement:
--   The Format construction uses the extend exp bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L424-L425
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L424-L425

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.extend_exp_bot {F : Format} (h : F.exp = ⊥) (k : ℕ) : (F.extend k).exp = ⊥ := by sorry
