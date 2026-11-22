-- Prove2me | Theorems.Thm_Fpy_DigitBound_Term_eval_decode
-- name    : Fpy.DigitBound.Term.eval_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:29.112654+00:00
-- url     : https://prove2.me/theorems/9f608277-e0f8-4dee-9466-dc390e11a180
-- title:
--   Term: eval decode
-- statement:
--   The encoding is exact, and never both `+∞` and `−∞`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L109-L157
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L109-L157

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.Term.eval_decode (M : IModel) : ∀ t : Term,
    ¬(t.enc.top.holds M ∧ t.enc.bot.holds M) ∧
      t.eval M.decode = decodeE (t.enc.top.holds M) (t.enc.bot.holds M) (t.enc.val.eval M)
  := by sorry
