-- Prove2me | Theorems.Thm_Mpfx_Format_exists_zpow_gt
-- name    : Mpfx.Format.exists_zpow_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:03.310519+00:00
-- url     : https://prove2.me/theorems/1102c3a0-8473-4be6-b2ed-a8e8a2486f1e
-- title:
--   Format: exists zpow gt
-- statement:
--   Above any real there is a power of two, at an exponent above `e`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L164-L171
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L164-L171

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.exists_zpow_gt (r : ℝ) (e : QExp) :
    ∃ k : ℤ, e ≤ (k : QExp) ∧ r < (2 : ℝ) ^ k := by sorry
