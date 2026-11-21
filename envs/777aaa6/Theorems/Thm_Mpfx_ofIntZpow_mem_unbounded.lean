-- Prove2me | Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
-- name    : Mpfx.ofIntZpow_mem_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:40:08.305492+00:00
-- url     : https://prove2.me/theorems/5cb76c4a-6339-4c97-ad37-019cfbe09510
-- title:
--   Mpfx: of Int Zpow mem unbounded
-- statement:
--   `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
--   `F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
--   is handled by `precisionAtMost_of_abs_le`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/CanonicalExp.lean#L82-L99
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/CanonicalExp.lean#L82-L99

import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_CanonicalExp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ofIntZpow_mem_unbounded (F : FiniteFormat) {k e : ℤ}
    (he_ge : ∀ {e' : ℤ}, F.exp = (e' : QExp) → e' ≤ e)
    (hk_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |k| ≤ (2 : ℤ) ^ p) :
    Dyadic.ofIntZpow k e ∈ F.unbounded := by sorry
