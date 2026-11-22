-- Prove2me | Theorems.Thm_Mpfx_not_isUndefined_awayZero
-- name    : Mpfx.not_isUndefined_awayZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:20.32637+00:00
-- url     : https://prove2.me/theorems/9972d7d2-dc28-4b8a-8313-490d12e9a072
-- title:
--   Mpfx: not is Undefined away Zero
-- statement:
--   The Mpfx construction uses the not is Undefined away Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L166-L168
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L166-L168

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.not_isUndefined_awayZero (F : FiniteFormat) :
    ¬ F.IsUndefined .awayZero := by sorry
