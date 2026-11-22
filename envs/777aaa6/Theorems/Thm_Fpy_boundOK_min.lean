-- Prove2me | Theorems.Thm_Fpy_boundOK_min
-- name    : Fpy.boundOK_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:41.589463+00:00
-- url     : https://prove2.me/theorems/f58cb915-585d-4adc-b9c9-bc821b6b3382
-- title:
--   Fpy: bound OK min
-- statement:
--   The Fpy construction uses the bound OK min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L161-L165
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L161-L165

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.boundOK_min {b : Bound} {d : NonNegDyadic} {x : Mpfx.Dyadic} (hb : Format.boundOK b x)
    (hx : |(x : ℚ)| ≤ ((d.1 : Mpfx.Dyadic) : ℚ)) : Format.boundOK (min b ↑d) x := by sorry
