-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRAZ_RNE
-- name    : Mpfx.Cex.no_roundsRAZ_RNE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:27.636785+00:00
-- url     : https://prove2.me/theorems/c9595c22-b94b-4f90-b414-7b506340f398
-- title:
--   Cex: no rounds RAZ RNE
-- statement:
--   **RAZ → RNE.** Adjacent values `u < u'` with `u ≥ 0` and `u'` even, and
--   `x = m − δ` just below their midpoint `m`: the intermediate RAZ lands in
--   `[m, u']`, where RNE returns `u'` (at `m` by the tie-break), but the direct RNE
--   returns the strictly nearer `u`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L351-L385
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L351-L385

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRAZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁.toFiniteFormat (.nearest .toEven) := by sorry
