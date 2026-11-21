-- Prove2me | Theorems.Thm_Mpfx_localDoubleRounding_of_above
-- name    : Mpfx.localDoubleRounding_of_above
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:47:41.677121+00:00
-- url     : https://prove2.me/theorems/6463d0db-fb35-4500-943d-2cbba992145d
-- title:
--   Mpfx: local Double Rounding of above
-- statement:
--   **Locality above the bound.** For the rules whose containment bounds `F₁` by
--   `next(b₁)`: an in-bound direct or double rounding puts its input below a value
--   of `F₁` within `next(b₁)`, since every rounding is faithful and so a larger input
--   rounds past `b₁`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L177-L218
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L177-L218

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.localDoubleRounding_of_above {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hmem : ∀ {T : Dyadic}, T ∈ F₁.unbounded →
      Format.boundOK F₁.toFormat.boundAfterNext T → T ∈ F₂)
    (rule : ∀ {T : NonNegDyadic}, T.val ∈ F₁.unbounded →
      Format.boundOK F₁.toFormat.boundAfterNext T.val →
      ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
        RoundsFinite (F₁.withBoundFF T) rm₁ (z : ℝ) w →
        RoundsFinite (F₁.withBoundFF T) rm₁ x w) :
    LocalDoubleRounding F₁ F₂ rm₁ rm₂ (BelowValue F₁ F₁.toFormat.boundAfterNext) := by sorry
