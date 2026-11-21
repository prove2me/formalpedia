-- Prove2me | Theorems.Thm_Mpfx_Format_extend_exp_coe
-- name    : Mpfx.Format.extend_exp_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:39.962169+00:00
-- url     : https://prove2.me/theorems/ad76f1fd-fb6f-433f-bc6c-a2d50c0e6e0f
-- title:
--   Format: extend exp coe
-- statement:
--   The Format construction uses the extend exp coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L420-L422
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L420-L422

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.extend_exp_coe {F : Format} {e : ℤ} (h : F.exp = e) (k : ℕ) :
    (F.extend k).exp = ((e - k : ℤ) : QExp) := by sorry
