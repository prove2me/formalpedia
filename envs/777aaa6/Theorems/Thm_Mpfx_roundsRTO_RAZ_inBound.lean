-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RAZ_inBound
-- name    : Mpfx.roundsRTO_RAZ_inBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:20.529002+00:00
-- url     : https://prove2.me/theorems/66dd5e32-8a6b-48ef-b969-700513a123af
-- title:
--   Mpfx: rounds RTO RAZ in Bound
-- statement:
--   **rnd-RTO-RAZ**, total form: the direct rounding overflows, or the rounding into
--   `F₂` and the double rounding stay in bound and agree with it. Nontriviality of `F₁`
--   forces `2 ≤ F₂.p` through the containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L582-L591
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L582-L591

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RAZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) := by sorry
