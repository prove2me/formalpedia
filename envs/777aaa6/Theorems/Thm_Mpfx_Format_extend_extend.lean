-- Prove2me | Theorems.Thm_Mpfx_Format_extend_extend
-- name    : Mpfx.Format.extend_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:23.111229+00:00
-- url     : https://prove2.me/theorems/0655e12e-db75-4744-aafd-7ff7ffc38adf
-- title:
--   Format: extend extend
-- statement:
--   Extending twice is extending by the sum.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L428-L434
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L428-L434

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.extend_extend (F : Format) (j k : ℕ) : (F.extend j).extend k = F.extend (j + k) := by sorry
