-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_mul_eq_finite
-- name    : Mpfx.WithSpecial.mul_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:27.054069+00:00
-- url     : https://prove2.me/theorems/fdfd46db-7b6a-4063-828f-d916c0d5cf84
-- title:
--   With Special: mul eq finite
-- statement:
--   A product is finite exactly when both factors are.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L126-L136
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L126-L136

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.mul_eq_finite {u v : WithSpecial Dyadic} {z : Dyadic} :
    u * v = finite z ↔ ∃ x y, u = finite x ∧ v = finite y ∧ z = x * y := by sorry
