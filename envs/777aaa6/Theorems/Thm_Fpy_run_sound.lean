-- Prove2me | Theorems.Thm_Fpy_run_sound
-- name    : Fpy.run_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:30.828445+00:00
-- url     : https://prove2.me/theorems/c2a761a5-3517-4d6f-b185-44e25d2bf216
-- title:
--   Fpy: run sound
-- statement:
--   Format inference for a whole program (A-Program): an argument described by
--   `a` gives a result described by `a'`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sound.lean#L350-L356
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sound.lean#L350-L356

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_FormatInference_Sound
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain} {A : Analysis L D} {Φ : Program L}

theorem Fpy.run_sound (hA : A.Sound Φ) {f : Fn} {y : Var} {s : Stmt L} {a a' : AVal D}
    {Γ' : AEnv D} (hΦ : Φ f = some (y, s)) (hs : AExec A Φ (.single y a) (some .real) s Γ' a')
    {v v' : Val} (hv : Describes a v) (hrun : Run Φ f v v') : Describes a' v' := by sorry
