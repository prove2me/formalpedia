-- Prove2me | Theorems.Thm_Fpy_Equiv_of_fwd
-- name    : Fpy.Equiv.of_fwd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:56.092975+00:00
-- url     : https://prove2.me/theorems/e3022966-cb8d-4108-a6e3-da401c596bf8
-- title:
--   Equiv: of fwd
-- statement:
--   An `Equiv` from one direction: by determinism, it suffices that `s'` runs
--   only where `s` does.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L125-L134
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L125-L134

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}

theorem Fpy.Equiv.of_fwd {Φ : Program L} {X : Set Var} {Γ : AEnv D} {κ : Option Val}
    {s s' : Stmt L}
    (hfwd : ∀ σ C o, Γ.Holds σ → Admits κ C → Exec Φ σ C s o →
      ∃ o', Exec Φ σ C s' o' ∧ o.Agree X o')
    (hrun : ∀ σ C o', Γ.Holds σ → Admits κ C → Exec Φ σ C s' o' → ∃ o, Exec Φ σ C s o) :
    Equiv Φ X Γ κ s s' := by sorry
