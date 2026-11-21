-- Prove2me | Theorems.Thm_Mpfx_Format_boundOK_mono
-- name    : Mpfx.Format.boundOK_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:29.608394+00:00
-- url     : https://prove2.me/theorems/e78eea90-14e4-48ba-a06a-4fb269f18664
-- title:
--   Format: bound OK mono
-- statement:
--   The magnitude-bound check is monotone in the bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L50-L60
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L50-L60

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.boundOK_mono {b₁ b₂ : Bound} (h : b₁ ≤ b₂) {x : Dyadic} :
    boundOK b₁ x → boundOK b₂ x := by sorry
