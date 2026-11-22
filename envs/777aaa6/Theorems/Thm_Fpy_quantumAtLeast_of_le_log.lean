-- Prove2me | Theorems.Thm_Fpy_quantumAtLeast_of_le_log
-- name    : Fpy.quantumAtLeast_of_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:47.181533+00:00
-- url     : https://prove2.me/theorems/54e87b65-30b5-445c-8369-3165a534825c
-- title:
--   Fpy: quantum At Least of le log
-- statement:
--   A nonzero value with at most `p` digits and magnitude at least `2^k` has
--   quantum at least `2^(k − p + 1)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L169-L188
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L169-L188

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.quantumAtLeast_of_le_log {p : ℕ} {k : ℤ} {d : Mpfx.Dyadic}
    (hp : Dyadic.precisionAtMost (p : Prec) d) (hd : (d : ℝ) ≠ 0)
    (hk : k ≤ Int.log 2 |(d : ℝ)|) : Dyadic.quantumAtLeast ((k - p + 1 : ℤ) : QExp) d := by sorry
