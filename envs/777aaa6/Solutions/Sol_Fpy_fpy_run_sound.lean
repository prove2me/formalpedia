-- Prove2me | solution 1 for Fpy.fpy_run_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:09.942992+00:00
-- url     : https://prove2.me/submissions/009cd6ca-18b5-45b9-87a1-8eac070dd47e

import Definitions.Def_Fpy_FormatInference_Refine
import Definitions.Def_Fpy_FormatInference_Analysis
import Theorems.Thm_Fpy_fpyAnalysis_sound
import Theorems.Thm_Fpy_run_sound


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}
namespace Fpy
theorem _root_.solution {Φ : Program (fpy decode)} {f : Fn} {y : Var} {s : Stmt (fpy decode)}
    {a a' : AVal (Fmt.domain c)} {Γ' : AEnv (Fmt.domain c)} (hΦ : Φ f = some (y, s))
    (hs : AExec (fpyAnalysis decode c) Φ (.single y a) (some .real) s Γ' a')
    {v v' : Val} (hv : Describes a v) (hrun : Run Φ f v v') : Describes a' v' :=
  run_sound (fpyAnalysis_sound Φ) hΦ hs hv hrun
end Fpy
