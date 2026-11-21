-- Prove2me | Theorems.Thm_Mpfx_Format_extend_mono
-- name    : Mpfx.Format.extend_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:44.91422+00:00
-- url     : https://prove2.me/theorems/a72502de-a3a9-4879-b082-0371b4acb46c
-- title:
--   Format: extend mono
-- statement:
--   `extend` is monotone in the bit count: `F.extend j ⊆ F.extend k` when `j ≤ k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L451-L463
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L451-L463

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.extend_mono (F : Format) {j k : ℕ} (h : j ≤ k) :
    F.extend j ⊆ F.extend k := by sorry
