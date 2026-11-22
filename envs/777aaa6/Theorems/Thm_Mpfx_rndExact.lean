-- Prove2me | Theorems.Thm_Mpfx_rndExact
-- name    : Mpfx.rndExact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:24.357061+00:00
-- url     : https://prove2.me/theorems/cdc3a623-9b01-4149-a090-b2749047fa62
-- title:
--   Mpfx: rnd Exact
-- statement:
--   **Exact-intermediate collapse.** If the input `v` is already representable
--   in the wide format `F₂`, double rounding is trivially correct for *any* modes:
--   the intermediate rounding fixes `v` (`z = v` by `RoundsFinite.eq_of_mem`), so
--   the double rounding of `v` is the direct one. This is the spec-relational
--   form of Flocq's `round_generic`-based collapse and the shared core of every
--   "exact intermediate" operation rule.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L29-L34
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L29-L34

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndExact {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {v : Dyadic} (hv : v ∈ F₂) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ (v : ℝ) z) (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ (v : ℝ) w := by sorry
