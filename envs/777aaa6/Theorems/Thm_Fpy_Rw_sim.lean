-- Prove2me | Theorems.Thm_Fpy_Rw_sim
-- name    : Fpy.Rw.sim
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:31.008938+00:00
-- url     : https://prove2.me/theorems/c052b4e7-ef55-4d6c-9161-c38b39ef4923
-- title:
--   Rw: sim
-- statement:
--   **Congruence**: rewriting sites, each under the `Γ` and `κ` format inference
--   assigns it, gives a statement that simulates the original.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L496-L499
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L496-L499

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)
variable {A Φ Φ' X}

theorem Fpy.Rw.sim (hA : A.Sound Φ) {Γ : AEnv D} {κ : Option Val} {s s' : Stmt L}
    (h : Rw A Φ Φ' X Γ κ s s') : Sim Φ Φ' X Γ κ s s' := by sorry
