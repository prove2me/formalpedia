-- Prove2me | Theorems.Thm_Mpfx_exp_le_log_of_mem
-- name    : Mpfx.exp_le_log_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:14.160182+00:00
-- url     : https://prove2.me/theorems/52846e39-1cdc-4282-8dd2-fdcd710501d1
-- title:
--   Mpfx: exp le log of mem
-- statement:
--   A positive `F`-value is at least the format's quantum, so `F.exp ≤ ⌊log₂ z⌋`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L474-L479
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L474-L479

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.exp_le_log_of_mem (F : FiniteFormat) {e : ℤ} (hexp : F.exp = (e : QExp))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    e ≤ Int.log 2 ((z : Dyadic) : ℝ) := by sorry
