-- Prove2me | Theorems.Thm_Mpfx_Dyadic_isRepresentableAtP_of_log
-- name    : Mpfx.Dyadic.isRepresentableAtP_of_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:16.788907+00:00
-- url     : https://prove2.me/theorems/7054d309-ba19-4dd2-b9f0-6a5cb66dbdd6
-- title:
--   Dyadic: is Representable At P of log
-- statement:
--   The `Int.log`-based bounds core: for `k ≠ 0` and `y = k · 2^e'`, the pair
--   `(k, e')` is the canonical representation of `y` at `log₂|k| + 1` bits. This
--   captures the `2^(nd-1) ≤ |k| < 2^nd` derivation (via `Int.zpow_log_le_self` /
--   `Int.lt_zpow_succ_log_self`) once.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L464-L500
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L464-L500

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic

theorem Mpfx.Dyadic.isRepresentableAtP_of_log {k e' : ℤ} (hk : k ≠ 0) {y : Dyadic}
    (hy : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e') :
    IsRepresentableAtP ((Int.log 2 (|k| : ℝ)).toNat + 1) k e' y := by sorry
