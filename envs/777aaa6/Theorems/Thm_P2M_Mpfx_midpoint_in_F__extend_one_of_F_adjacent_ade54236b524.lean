-- Prove2me | Theorems.Thm_P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524
-- name    : P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:50:43.536181+00:00
-- url     : https://prove2.me/theorems/53604240-cb02-49a5-94e8-301a11648b0d
-- title:
--   P2 M Mpfx midpoint in F  extend one of F adjacent ade54236b524: P2 M Mpfx midpoint in F  extend one of F adjacent ade54236b524
-- statement:
--   **Midpoint of adjacent values**, either sign, lies in `F.extend 1`: negative
--   pairs reflect to the positive case, and a pair at `0` is a halving.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Discrete.lean#L140-L198
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Discrete.lean#L140-L198

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Discrete
set_option autoImplicit true
open Mpfx

theorem P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524 {F : FiniteFormat}
    {y₁ y₂ : _root_.Mpfx.Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y₂ : _root_.Mpfx.Dyadic) : ℝ))
    (h_adj : ∀ y : _root_.Mpfx.Dyadic, y ∈ F →
              ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y : _root_.Mpfx.Dyadic) : ℝ) →
              ((y₂ : _root_.Mpfx.Dyadic) : ℝ) ≤ ((y : _root_.Mpfx.Dyadic) : ℝ)) :
    _root_.Mpfx.Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by sorry

alias «Mpfx».«midpoint_in_F₁_extend_one_of_F_adjacent» := P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524
