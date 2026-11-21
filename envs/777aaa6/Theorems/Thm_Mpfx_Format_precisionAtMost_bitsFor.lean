-- Prove2me | Theorems.Thm_Mpfx_Format_precisionAtMost_bitsFor
-- name    : Mpfx.Format.precisionAtMost_bitsFor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:27.508718+00:00
-- url     : https://prove2.me/theorems/0d0a7efa-f52e-4d1d-97e7-43b60ec90251
-- title:
--   Format: precision At Most bits For
-- statement:
--   A value with quantum `2^m` and magnitude at most `B` has a significand of
--   magnitude at most `⌊B / 2^m⌋`, so it needs at most `bitsFor B m` digits.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L269-L289
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L269-L289

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.precisionAtMost_bitsFor {x : Dyadic} {m : ℤ} {B : ℝ}
    (hq : Dyadic.quantumAtLeast (m : QExp) x) (hb : |(x : ℝ)| ≤ B) :
    Dyadic.precisionAtMost (bitsFor B m : Prec) x := by sorry
