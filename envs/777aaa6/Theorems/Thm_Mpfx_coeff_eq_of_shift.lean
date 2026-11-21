-- Prove2me | Theorems.Thm_Mpfx_coeff_eq_of_shift
-- name    : Mpfx.coeff_eq_of_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:17:55.945656+00:00
-- url     : https://prove2.me/theorems/4b902467-c891-479f-9b28-635777b09f31
-- title:
--   Mpfx: coeff eq of shift
-- statement:
--   Inverse of the shift: if two canonical reps of the same value agree with
--   `e₁ ≤ e₂`, the finer coefficient is the coarser one scaled by `2^(e₂-e₁)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L71-L75
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L71-L75

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.coeff_eq_of_shift {K : Type*} [Field K] [CharZero K] {c₁ c₂ e₁ e₂ : ℤ} (h : e₁ ≤ e₂)
    (heq : (c₁ : K) * (2 : K) ^ e₁ = (c₂ : K) * (2 : K) ^ e₂) :
    c₁ = c₂ * (2 : ℤ) ^ (e₂ - e₁).toNat := by sorry
