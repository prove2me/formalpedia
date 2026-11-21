-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_add_eq_finite
-- name    : Mpfx.WithSpecial.add_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:43.850482+00:00
-- url     : https://prove2.me/theorems/42e8dd9a-b93a-41b4-9e27-50551df4ccfc
-- title:
--   With Special: add eq finite
-- statement:
--   A sum is finite exactly when both summands are.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L139-L149
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L139-L149

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.add_eq_finite {u v : WithSpecial Dyadic} {z : Dyadic} :
    u + v = finite z ↔ ∃ x y, u = finite x ∧ v = finite y ∧ z = x + y := by sorry
