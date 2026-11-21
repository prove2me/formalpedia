-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_expBot
-- name    : Mpfx.canonicalExp_expBot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:19.266764+00:00
-- url     : https://prove2.me/theorems/47b38fb1-9b9b-40b8-9b8d-d82801fb6247
-- title:
--   Mpfx: canonical Exp exp Bot
-- statement:
--   Closed form of `canonicalExp` with no minimum quantum (`exp = ⊥`):
--   `log₂|v| + 1 − p` (the vacuous-normality case of `canonicalExp_closed`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L427-L430
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L427-L430

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_expBot {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = ⊥)
    {v : ℝ} (hv : v ≠ 0) : F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) := by sorry
