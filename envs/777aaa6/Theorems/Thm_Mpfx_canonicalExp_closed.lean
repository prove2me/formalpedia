-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_closed
-- name    : Mpfx.canonicalExp_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:41.464651+00:00
-- url     : https://prove2.me/theorems/57f610e4-4f6c-428d-abda-a270b0bf968a
-- title:
--   Mpfx: canonical Exp closed
-- statement:
--   **Closed form of `canonicalExp` in the normal range**, uniform over both
--   exponent regimes. When `v` is nonzero and its precision exponent
--   `log₂|v| + 1 − p` is at least `F.exp` (the *normal* regime — vacuous for
--   `exp = ⊥`), `canonicalExp` takes that form.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L413-L423
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L413-L423

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_closed {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) {v : ℝ} (hv : v ≠ 0)
    (hnorm : F.exp ≤ ((Int.log 2 |v| + 1 - (p : ℤ) : ℤ) : QExp)) :
    F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) := by sorry
