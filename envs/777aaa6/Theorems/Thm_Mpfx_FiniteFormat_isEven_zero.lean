-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
-- name    : Mpfx.FiniteFormat.isEven_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:40:52.812193+00:00
-- url     : https://prove2.me/theorems/2e62decc-c23c-478c-a992-ab64349ccfc2
-- title:
--   Finite Format: is Even zero
-- statement:
--   The Finite Format construction uses the is Even zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L82-L83
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L82-L83

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isEven_zero (F : FiniteFormat) : IsEven F 0 := by sorry
