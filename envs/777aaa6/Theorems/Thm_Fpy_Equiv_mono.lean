-- Prove2me | Theorems.Thm_Fpy_Equiv_mono
-- name    : Fpy.Equiv.mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:25.180804+00:00
-- url     : https://prove2.me/theorems/96e2d42b-89c9-4a0a-ad5b-ee18d4673fdb
-- title:
--   Equiv: mono
-- statement:
--   The Equiv construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L136-L140
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L136-L140

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}

theorem Fpy.Equiv.mono {Φ : Program L} {X Y : Set Var} {Γ : AEnv D} {κ : Option Val}
    {s s' : Stmt L} (h : Equiv Φ X Γ κ s s') (hXY : X ⊆ Y) : Equiv Φ Y Γ κ s s' := by sorry
