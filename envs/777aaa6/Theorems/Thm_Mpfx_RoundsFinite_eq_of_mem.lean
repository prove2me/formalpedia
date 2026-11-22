-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
-- name    : Mpfx.RoundsFinite.eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:08.774575+00:00
-- url     : https://prove2.me/theorems/108c0f1d-5d00-4b99-ae4f-6b46feca3522
-- title:
--   Rounds Finite: eq of mem
-- statement:
--   **Rounding fixes representable values** — the spec-relational form of
--   Flocq's `round_generic` (paper Def. 7: `∀ f ∈ F, ◦(f) = f`). If `d ∈ F` and
--   `y` is the `rm`-rounding of `(d : ℝ)` in `F`, then `y = d`, for *any* mode `rm`
--   (including the degenerate `IsUndefined` formats — `RoundsFinite` never consults
--   `IsUndefined`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L293-L295
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L293-L295

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.eq_of_mem {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic}
    (hd : d ∈ F) {y : Dyadic} (h : RoundsFinite F rm (d : ℝ) y) : y = d := by sorry
