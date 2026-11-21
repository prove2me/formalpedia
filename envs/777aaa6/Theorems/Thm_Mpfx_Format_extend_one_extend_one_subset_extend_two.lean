-- Prove2me | Theorems.Thm_Mpfx_Format_extend_one_extend_one_subset_extend_two
-- name    : Mpfx.Format.extend_one_extend_one_subset_extend_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:26.916061+00:00
-- url     : https://prove2.me/theorems/569e76ee-4924-4e20-be0d-79b031f7acc7
-- title:
--   Format: extend one extend one subset extend two
-- statement:
--   `(F.extend 1).extend 1 ⊆ F.extend 2`, by `extend_extend`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L466-L468
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L466-L468

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.extend_one_extend_one_subset_extend_two (F : Format) :
    (F.extend 1).extend 1 ⊆ F.extend 2 := by sorry
