-- Prove2me | Theorems.Thm_Mpfx_ulp_le_half_ulp_of_canonicalExp_lt
-- name    : Mpfx.ulp_le_half_ulp_of_canonicalExp_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:34.855562+00:00
-- url     : https://prove2.me/theorems/a17ac2d0-e6bc-4d2d-9a3e-6da5345c77d8
-- title:
--   Mpfx: ulp le half ulp of canonical Exp lt
-- statement:
--   If `F₂`'s canonical exponent at `x` is strictly below `F₁`'s, then
--   `ulp F₂ x ≤ ulp F₁ x / 2` (integer exponents differ by at least one).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L165-L173
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L165-L173

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ulp_le_half_ulp_of_canonicalExp_lt {F₁ F₂ : FiniteFormat} {x : ℝ}
    (hx : x ≠ 0) (h : F₂.canonicalExp x < F₁.canonicalExp x) :
    ulp F₂ x ≤ ulp F₁ x / 2 := by sorry
