-- Prove2me | Theorems.Thm_Mpfx_int_mul_two_zpow_le_iff
-- name    : Mpfx.int_mul_two_zpow_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:19.478611+00:00
-- url     : https://prove2.me/theorems/f211632f-2f79-43aa-aa1c-457c4384ef4c
-- title:
--   Mpfx: int mul two zpow le iff
-- statement:
--   The Mpfx construction uses the int mul two zpow le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L122-L124
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L122-L124

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.int_mul_two_zpow_le_iff {a b k : ℤ} :
    (a : ℝ) * (2 : ℝ) ^ k ≤ (b : ℝ) * (2 : ℝ) ^ k ↔ a ≤ b := by sorry
