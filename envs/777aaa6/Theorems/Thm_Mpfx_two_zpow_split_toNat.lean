-- Prove2me | Theorems.Thm_Mpfx_two_zpow_split_toNat
-- name    : Mpfx.two_zpow_split_toNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:13.945183+00:00
-- url     : https://prove2.me/theorems/70180c78-9f10-4add-b56b-005f24ad34cc
-- title:
--   Mpfx: two zpow split to Nat
-- statement:
--   Split `2 ^ e₁ = 2 ^ (e₁ - e₂).toNat * 2 ^ e₂` when `e₂ ≤ e₁`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L19-L22
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L19-L22

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_zpow_split_toNat {K : Type*} [Field K] [CharZero K] {e₁ e₂ : ℤ} (h : e₂ ≤ e₁) :
    (2 : K) ^ e₁ = (2 : K) ^ (e₁ - e₂).toNat * (2 : K) ^ e₂ := by sorry
