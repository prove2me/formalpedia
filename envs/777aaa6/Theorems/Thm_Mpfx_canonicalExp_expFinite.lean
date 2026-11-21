-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_expFinite
-- name    : Mpfx.canonicalExp_expFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:54.532897+00:00
-- url     : https://prove2.me/theorems/7effd9cd-3146-4629-a35b-b760b9506e27
-- title:
--   Mpfx: canonical Exp exp Finite
-- statement:
--   Closed form of `canonicalExp` with a minimum quantum (`exp = emin` finite):
--   `max(log₂|v| + 1 − p, emin)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L434-L438
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L434-L438

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_expFinite {F : FiniteFormat} {p : ℕ} {emin : ℤ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = (emin : QExp))
    {v : ℝ} (hv : v ≠ 0) :
    F.canonicalExp v = max (Int.log 2 |v| + 1 - (p : ℤ)) emin := by sorry
