-- Prove2me | Theorems.Thm_Mpfx_Format_withBound_mono
-- name    : Mpfx.Format.withBound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:18.479031+00:00
-- url     : https://prove2.me/theorems/59e0c3fe-2f56-447f-aabc-92b00efecea5
-- title:
--   Format: with Bound mono
-- statement:
--   Relaxing the bound enlarges the format.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L36-L38
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L36-L38

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.withBound_mono (F : Format) {b b' : Bound} (h : ∀ v, boundOK b v → boundOK b' v) :
    F.withBound b ⊆ F.withBound b' := by sorry
