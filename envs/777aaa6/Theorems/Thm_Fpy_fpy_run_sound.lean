-- Prove2me | Theorems.Thm_Fpy_fpy_run_sound
-- name    : Fpy.fpy_run_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:35:58.246776+00:00
-- url     : https://prove2.me/theorems/4473a6ff-7515-437e-83a4-dcf6b3234225
-- title:
--   Fpy: fpy run sound
-- statement:
--   **Theorem 4.1** for FPy: a program's result lies in the format inferred for
--   it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean#L114-L118
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean#L114-L118

import Definitions.Def_Fpy_FormatInference_Refine
import Definitions.Def_Fpy_FormatInference_Analysis
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}

theorem Fpy.fpy_run_sound {Φ : Program (fpy decode)} {f : Fn} {y : Var} {s : Stmt (fpy decode)}
    {a a' : AVal (Fmt.domain c)} {Γ' : AEnv (Fmt.domain c)} (hΦ : Φ f = some (y, s))
    (hs : AExec (fpyAnalysis decode c) Φ (.single y a) (some .real) s Γ' a')
    {v v' : Val} (hv : Describes a v) (hrun : Run Φ f v v') : Describes a' v' := by sorry
