-- Prove2me | Theorems.Thm_Mpfx_Format_shrink_extend_one
-- name    : Mpfx.Format.shrink_extend_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:45.785707+00:00
-- url     : https://prove2.me/theorems/8d523ba0-a71b-4fe4-9fd4-75bb062488bb
-- title:
--   Format: shrink extend one
-- statement:
--   The Format construction uses the shrink extend one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L560-L569
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L560-L569

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.shrink_extend_one (F : Format) : (F.extend 1).shrink = F := by sorry
