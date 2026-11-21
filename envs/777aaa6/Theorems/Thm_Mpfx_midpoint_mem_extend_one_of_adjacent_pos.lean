-- Prove2me | Theorems.Thm_Mpfx_midpoint_mem_extend_one_of_adjacent_pos
-- name    : Mpfx.midpoint_mem_extend_one_of_adjacent_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:09.041342+00:00
-- url     : https://prove2.me/theorems/4de2a056-9fcb-420e-94e8-38943af7b294
-- title:
--   Mpfx: midpoint mem extend one of adjacent pos
-- statement:
--   **Midpoint of adjacent positive values.** The next power of two above `y₁`
--   is at least `y₂`, so the midpoint stays in `y₁`'s binade and has `y₁`'s step
--   `2^c`. Both endpoints are multiples of `2^c`, so the midpoint is a multiple of
--   `2^(c−1)`, the step of `F.extend 1` there.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Discrete.lean#L45-L95
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Discrete.lean#L45-L95

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Discrete
set_option autoImplicit true
open Mpfx

theorem Mpfx.midpoint_mem_extend_one_of_adjacent_pos (F : FiniteFormat)
    {y₁ y₂ : _root_.Mpfx.Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : _root_.Mpfx.Dyadic) : ℝ))
    (h_lt : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y₂ : _root_.Mpfx.Dyadic) : ℝ))
    (h_adj : ∀ y : _root_.Mpfx.Dyadic, y ∈ F →
              ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y : _root_.Mpfx.Dyadic) : ℝ) →
              ((y₂ : _root_.Mpfx.Dyadic) : ℝ) ≤ ((y : _root_.Mpfx.Dyadic) : ℝ)) :
    _root_.Mpfx.Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by sorry
