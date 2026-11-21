-- Prove2me | Theorems.Thm_Fpy_Exec_frame
-- name    : Fpy.Exec.frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:49:59.961438+00:00
-- url     : https://prove2.me/theorems/c37e74e9-de28-49f2-9431-23a0935f324f
-- title:
--   Exec: frame
-- statement:
--   A statement leaves every variable it does not assign unchanged.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean#L174-L192
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean#L174-L192

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Fpy_Semantics
set_option autoImplicit true
open Fpy
variable {L : Signature}
variable (Φ : Program L)

theorem Fpy.Exec.frame : ∀ {σ : Store} {C : Val} {s : Stmt L} {o : Outcome} {σ' : Store},
    Exec Φ σ C s o → o = .normal σ' → ∀ x ∉ s.assigned, σ' x = σ x
  := by sorry
