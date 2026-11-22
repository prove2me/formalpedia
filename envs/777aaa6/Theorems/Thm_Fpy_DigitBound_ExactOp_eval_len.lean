-- Prove2me | Theorems.Thm_Fpy_DigitBound_ExactOp_eval_len
-- name    : Fpy.DigitBound.ExactOp.eval_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:42.587173+00:00
-- url     : https://prove2.me/theorems/29155c78-78a6-4db2-a46b-c0fc2716a2a5
-- title:
--   Exact Op: eval len
-- statement:
--   The Exact Op construction uses the eval len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L405-L409
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L405-L409

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.ExactOp.eval_len {vs : List Val} {v : Val} (h : ExactOp.len.eval vs = some v) :
    ∃ k : ℕ, v = .num (.finite k) := by sorry
