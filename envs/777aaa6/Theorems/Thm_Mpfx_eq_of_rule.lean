-- Prove2me | Theorems.Thm_Mpfx_eq_of_rule
-- name    : Mpfx.eq_of_rule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:14.732583+00:00
-- url     : https://prove2.me/theorems/117b6ea7-0045-47ab-8fcd-cea807d214b8
-- title:
--   Mpfx: eq of rule
-- statement:
--   Agreement from a finite rule at `F₁` with bound `B`: when the double rounding
--   and the direct rounding are both within `B`, restrict the double rounding,
--   compose, and lift.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L78-L86
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L78-L86

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.eq_of_rule {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) {B : Bound}
    (rule : ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
      RoundsFinite (F₁.withBoundFF B) rm₁ (z : ℝ) w → RoundsFinite (F₁.withBoundFF B) rm₁ x w)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsFinite F₂.unbounded rm₂ x z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) (hy : RoundsFinite F₁.unbounded rm₁ x y)
    (hwB : Format.boundOK B w) (hyB : Format.boundOK B y) : w = y := by sorry
