-- Prove2me | Theorems.Thm_Mpfx_two_zpow_shift
-- name    : Mpfx.two_zpow_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:17:59.663146+00:00
-- url     : https://prove2.me/theorems/b84098a1-bdfb-4a4c-8383-37ee51b38444
-- title:
--   Mpfx: two zpow shift
-- statement:
--   Re-base a canonical rep to a coarser exponent: shift `c·2^e` down to quantum
--   `k ≤ e`, folding the extra powers of two into an integer coefficient.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L65-L67
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L65-L67

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_zpow_shift {K : Type*} [Field K] [CharZero K] (c : ℤ) {e k : ℤ} (h : k ≤ e) :
    (c : K) * (2 : K) ^ e = ((c * (2 : ℤ) ^ (e - k).toNat : ℤ) : K) * (2 : K) ^ k := by sorry
