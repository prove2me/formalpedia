-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_subnormal
-- name    : Mpfx.canonicalExp_subnormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:09.990331+00:00
-- url     : https://prove2.me/theorems/0fd155b2-e781-496e-a334-fc373bae04ca
-- title:
--   Mpfx: canonical Exp subnormal
-- statement:
--   Closed form in the **subnormal** range: when the precision exponent falls
--   below the quantum, `canonicalExp` *is* the quantum.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L455-L458
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L455-L458

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_subnormal {F : FiniteFormat} {p : ℕ} {emin : ℤ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = (emin : QExp)) {v : ℝ} (hv : v ≠ 0)
    (h : Int.log 2 |v| + 1 - (p : ℤ) ≤ emin) : F.canonicalExp v = emin := by sorry
