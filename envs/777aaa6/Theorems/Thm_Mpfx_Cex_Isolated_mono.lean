-- Prove2me | Theorems.Thm_Mpfx_Cex_Isolated_mono
-- name    : Mpfx.Cex.Isolated.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:53:32.559515+00:00
-- url     : https://prove2.me/theorems/dfa5e85f-6c3f-429e-b9d4-d297ada570b4
-- title:
--   Isolated: mono
-- statement:
--   The Isolated construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L24-L26
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L24-L26

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.Isolated.mono {F : FiniteFormat} {m : Dyadic} {K K' : ℤ} (h : Isolated F m K)
    (hK : K' ≤ K) : Isolated F m K' := by sorry
