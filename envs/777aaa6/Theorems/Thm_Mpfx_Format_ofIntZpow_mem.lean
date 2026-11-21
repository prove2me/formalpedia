-- Prove2me | Theorems.Thm_Mpfx_Format_ofIntZpow_mem
-- name    : Mpfx.Format.ofIntZpow_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:42.342161+00:00
-- url     : https://prove2.me/theorems/0661437a-d524-4f44-ac9d-d5c3a79e2396
-- title:
--   Format: of Int Zpow mem
-- statement:
--   `c · 2^k` lies in `F` once the three constraints are checked.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L215-L219
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L215-L219

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.ofIntZpow_mem {F : Format} {c k : ℤ}
    (hp : Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow c k))
    (he : F.exp ≤ (k : QExp)) (hb : boundOK F.b (Dyadic.ofIntZpow c k)) :
    Dyadic.ofIntZpow c k ∈ F := by sorry
