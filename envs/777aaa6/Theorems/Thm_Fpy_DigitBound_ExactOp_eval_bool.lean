-- Prove2me | Theorems.Thm_Fpy_DigitBound_ExactOp_eval_bool
-- name    : Fpy.DigitBound.ExactOp.eval_bool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:40.415184+00:00
-- url     : https://prove2.me/theorems/062ed9fe-745a-4ce8-be90-58582e3c7106
-- title:
--   Exact Op: eval bool
-- statement:
--   The Exact Op construction uses the eval bool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L399-L403
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L399-L403

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.ExactOp.eval_bool {op : ExactOp} {vs : List Val} {v : Val} (h : op.eval vs = some v)
    (hop : op ≠ .len) : ∃ b, v = .bool b := by sorry
