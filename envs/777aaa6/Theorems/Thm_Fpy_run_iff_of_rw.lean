-- Prove2me | Theorems.Thm_Fpy_run_iff_of_rw
-- name    : Fpy.run_iff_of_rw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:18.48444+00:00
-- url     : https://prove2.me/theorems/08c51fc8-819c-429f-b647-0a37f90b8f0c
-- title:
--   Fpy: run iff of rw
-- statement:
--   **Rewriting preserves semantics**: if the entry function's body is
--   rewritten under format inference from an argument bound `a`, the program
--   returns the same values on every argument `a` describes.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L519-L536
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L519-L536

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)
variable {A Φ Φ' X}

theorem Fpy.run_iff_of_rw (hA : A.Sound Φ) {f : Fn} {y : Var} {s s' : Stmt L} {a : AVal D}
    (hΦ : Φ f = some (y, s)) (hΦ' : Φ' f = some (y, s'))
    (h : Rw A Φ Φ' X (.single y a) (some .real) s s') {v v' : Val} (hv : Describes a v) :
    Run Φ f v v' ↔ Run Φ' f v v' := by sorry
