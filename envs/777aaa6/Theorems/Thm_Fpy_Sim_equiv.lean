-- Prove2me | Theorems.Thm_Fpy_Sim_equiv
-- name    : Fpy.Sim.equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:12.94522+00:00
-- url     : https://prove2.me/theorems/afc0806a-841c-4044-99f1-63bba1c3a9a2
-- title:
--   Sim: equiv
-- statement:
--   A rewrite at a site: `s` rewritten to `s₁` within, then `s₁` to `s'` by a
--   correct rewrite whose `Γ` binds no fresh variable.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L503-L514
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L503-L514

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)
variable {A Φ Φ' X}

theorem Fpy.Sim.equiv {Γ : AEnv D} {κ : Option Val} {s s₁ s' : Stmt L}
    (h : Sim Φ Φ' X Γ κ s s₁) (h' : Equiv Φ' X Γ κ s₁ s') (hX : ∀ x ∈ X, Γ x = none) :
    Sim Φ Φ' X Γ κ s s' := by sorry
