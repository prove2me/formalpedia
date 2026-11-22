-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_ofIntZpow_mem_shrink_iff
-- name    : Mpfx.FiniteFormat.ofIntZpow_mem_shrink_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:14.726377+00:00
-- url     : https://prove2.me/theorems/bf9955b4-cb96-4a38-a9fa-b4781d55e272
-- title:
--   Finite Format: of Int Zpow mem shrink iff
-- statement:
--   **Alternation at the canonical step.** A multiple `k · 2^e` of a step at
--   least the quantum, whose own canonical exponent is at least `e`, lies in the
--   shrink exactly when `k` is even.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L237-L276
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L237-L276

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.ofIntZpow_mem_shrink_iff (F : FiniteFormat) (h : F.p ≠ ((1 : ℕ) : Prec))
    {k e : ℤ} (he : F.exp ≤ (e : QExp)) (hk : ∀ p : ℕ, F.p = p → |k| ≤ 2 ^ p)
    (hce : k ≠ 0 → e ≤ F.canonicalExp (Dyadic.ofIntZpow k e)) :
    Dyadic.ofIntZpow k e ∈ (F.shrink h).unbounded ↔ Even k := by sorry
