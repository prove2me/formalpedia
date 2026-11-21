-- Prove2me | Theorems.Thm_Fpy_Store_Agree_mono
-- name    : Fpy.Store.Agree.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:49:47.486182+00:00
-- url     : https://prove2.me/theorems/7ddd8a93-1550-451f-96c2-d38dbcc51f8d
-- title:
--   Agree: mono
-- statement:
--   The Agree construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L56-L57
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L56-L57

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {X : Set Var}

theorem Fpy.Store.Agree.mono {Y : Set Var} {σ σ' : Store} (h : σ.Agree X σ') (hXY : X ⊆ Y) :
    σ.Agree Y σ' := by sorry
