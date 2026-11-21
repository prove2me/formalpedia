-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_pTop
-- name    : Mpfx.canonicalExp_pTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:33.553454+00:00
-- url     : https://prove2.me/theorems/6a0852e6-bc7f-4239-a954-a87d39f3ece3
-- title:
--   Mpfx: canonical Exp p Top
-- statement:
--   Closed form with unrestricted precision: `canonicalExp` is the quantum
--   everywhere (`F.finite` rules out `exp = ⊥` here).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L449-L451
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L449-L451

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_pTop {F : FiniteFormat} {emin : ℤ}
    (hp : F.p = ⊤) (hexp : F.exp = (emin : QExp)) (v : ℝ) : F.canonicalExp v = emin := by sorry
