-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_le_iff
-- name    : Mpfx.FiniteFormat.canonicalExp_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:05.364778+00:00
-- url     : https://prove2.me/theorems/544d4356-36c6-4ad3-ae6d-dd79d8ac5eeb
-- title:
--   Finite Format: canonical Exp le iff
-- statement:
--   **Upper bounds on `canonicalExp`.** Away from `0`, `canonicalExp x ≤ k` says
--   exactly that both constraints the format imposes — the precision exponent
--   `⌊log₂|x|⌋ + 1 − p` and the minimum quantum — are at most `k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L316-L330
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L316-L330

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.canonicalExp_le_iff (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {k : ℤ} :
    F.canonicalExp x ≤ k ↔
      (∀ p : ℕ, F.p = p → Int.log 2 |x| + 1 - p ≤ k) ∧ (∀ e : ℤ, F.exp = e → e ≤ k) := by sorry
