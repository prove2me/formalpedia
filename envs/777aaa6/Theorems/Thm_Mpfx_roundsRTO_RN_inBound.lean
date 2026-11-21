-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RN_inBound
-- name    : Mpfx.roundsRTO_RN_inBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:17.949741+00:00
-- url     : https://prove2.me/theorems/5b9c8497-015e-4e8f-b521-2d9d3c3990cc
-- title:
--   Mpfx: rounds RTO RN in Bound
-- statement:
--   **rnd-RTO-RN**, total form: the direct rounding overflows, or the rounding into `F₂`
--   and the double rounding stay in bound and agree with it. Nontriviality of `F₁` forces `2
--   ≤ F₂.p` through the containment; `F₁` must support the tie-break (vacuous for RNA).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L605-L615
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L605-L615

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RN_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) (x : ℝ) :
    Overflows F₁ (.nearest tb) x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ (.nearest tb) (z : ℝ) w ∧
      RoundsInBound F₁ (.nearest tb) x w) := by sorry
